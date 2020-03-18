{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE BinaryLiterals #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UnboxedSums #-}
{-# LANGUAGE UnboxedTuples #-}

-- | Implementation of static hash map data structure.
module Data.Bytes.HashMap
  ( Map
  , lookup
  , fromList
  , fromListWith
    -- * Used for testing
  , HashMapException(..)
  ) where

import Prelude hiding (lookup)

import Control.Exception (Exception,throwIO)
import Control.Monad (when)
import Data.Bits ((.&.),complement)
import Data.Bytes.Types (Bytes(Bytes))
import Data.Foldable (for_,foldlM)
import Data.Ord (Down(Down))
import Data.Primitive (ByteArray,ByteArray(..))
import Data.Primitive.SmallArray (SmallArray(..))
import Data.Primitive.Unlifted.Array (UnliftedArray(..))
import GHC.Exts (Int(I#),SmallArray#,ByteArray#,ArrayArray#,Int#)
import GHC.Word (Word(W#),Word32)
import System.Entropy (CryptHandle,hGetEntropy)

import qualified Data.ByteString as ByteString
import qualified Data.ByteString.Unsafe as ByteString
import qualified Data.Bytes as Bytes
import qualified Data.Bytes.Hash as Hash
import qualified Data.List as List
import qualified Data.Primitive as PM
import qualified Data.Primitive.Ptr as PM
import qualified Data.Primitive.Unlifted.Array as PM
import qualified GHC.Exts as Exts

-- | A static perfect hash table where the keys are byte arrays. This
--   table cannot be updated after its creation, but all lookups have
--   guaranteed O(1) worst-case cost. It consumes linear space. This
--   is an excellent candidate for use with compact regions.
data Map v = Map
  !ByteArray -- top-level entropy
  !(UnliftedArray ByteArray) -- entropies
  !(UnliftedArray ByteArray) -- keys
  !(SmallArray v) -- values
  deriving stock (Functor,Foldable,Traversable)

fromList :: CryptHandle -> [(Bytes,v)] -> IO (Map v)
fromList h = fromListWith h const

lookup :: Bytes -> Map v -> Maybe v
{-# inline lookup #-}
lookup
  (Bytes (ByteArray keyArr) (I# keyOff) (I# keyLen))
  (Map (ByteArray entropyA) (UnliftedArray entropies) (UnliftedArray keys) (SmallArray vals)) =
    case lookup# (# keyArr,keyOff,keyLen #) (# entropyA,entropies,keys,vals #) of
      (# (# #) | #) -> Nothing
      (# | v #) -> Just v

lookup# ::
     (# ByteArray#, Int#, Int# #)
  -> (# ByteArray#, ArrayArray#, ArrayArray#, SmallArray# v #)
  -> (# (# #) | v #)
{-# noinline lookup# #-}
lookup# (# keyArr#, keyOff#, keyLen# #) (# entropyA#, entropies#, keys#, vals# #)
  | sz == 0 = (# (# #) | #)
  | PM.sizeofByteArray entropyA < reqEntropy = (# (# #) | #)
  | entropyB <- PM.indexUnliftedArray entropies (w2i (unsafeRem (upW32 (Hash.bytes entropyA key)) (i2w sz))),
    PM.sizeofByteArray entropyB >= reqEntropy,
    ix <- w2i (unsafeRem (upW32 (Hash.bytes entropyB key)) (i2w sz)),
    bytesEqualsByteArray key (PM.indexUnliftedArray keys ix),
    (# v #) <- PM.indexSmallArray## vals ix = (# | v #)
  | otherwise = (# (# #) | #)
  where
  sz = PM.sizeofUnliftedArray entropies
  reqEntropy = w2i (requiredEntropy (i2w (Bytes.length key)))
  key = Bytes (ByteArray keyArr#) (I# keyOff#) (I# keyLen#)
  entropyA = ByteArray entropyA#
  entropies = UnliftedArray entropies# :: UnliftedArray ByteArray
  keys = UnliftedArray keys# :: UnliftedArray ByteArray
  vals = SmallArray vals#

unsafeRem :: Word -> Word -> Word
unsafeRem (W# a) (W# b) = W# (Exts.remWord# a b)

fromListWith :: forall v.
     CryptHandle -- ^ Source of randomness
  -> (v -> v -> v)
  -> [(Bytes,v)]
  -> IO (Map v)
fromListWith h combine xs
  | count == 0 = pure (Map mempty mempty mempty mempty)
  | otherwise = do
      let maxLen' = w2i $ requiredEntropy $ i2w $
            List.foldl' (\acc (b,_) -> max (Bytes.length b) acc) 0 xs'
          allowedCollisions = ceiling (sqrt (fromIntegral @Int @Double (count + 1))) :: Int
      entropyA <- findInitialEntropy h maxLen' count allowedCollisions xs'
      let groups :: [[(Word,(Bytes,v))]]
          groups = List.sortOn (Down . List.length @[])
            (List.groupBy (\(x,_) (y,_) -> x == y)
              (List.sortOn fst
                (List.map
                  (\(b,v) -> (rem (fromIntegral @Word32 @Word (Hash.bytes entropyA b)) (i2w count), (b,v)))
                  xs'
                )
              )
            )
      used <- PM.newSmallArray count False
      keys <- PM.newUnliftedArray count (mempty :: ByteArray)
      values <- PM.newSmallArray count (errorThunk @v)
      entropies <- PM.newUnliftedArray count (mempty :: ByteArray)
      let {-# SCC goB #-}
          goB [] = pure ()
          goB (x : ps) = do
            let ix = w2i (unsafeHeadFst x)
                keyVals = map snd x
                maxGroupLen = List.foldl' (\acc (b,_) -> max (Bytes.length b) acc) 0 keyVals
            goC 100000 ix keyVals (w2i (requiredEntropy (i2w maxGroupLen))) ps
          {-# SCC goC #-}
          goC :: Int -> Int -> [(Bytes,v)] -> Int -> [[(Word,(Bytes,v))]] -> IO ()
          goC !counter !ix keyVals !entropySz zs = do
            entropy <- askForEntropy h entropySz
            tmpUsed <- PM.cloneSmallMutableArray used 0 count
            allGood <- foldlM
              (\good (key,_) -> if good
                then do
                  let j = fromIntegral @Word @Int (rem (upW32 (Hash.bytes entropy key)) (i2w count))
                  PM.readSmallArray tmpUsed j >>= \case
                    True -> pure False
                    False -> do
                      PM.writeSmallArray tmpUsed j True
                      pure True
                else pure False
              ) True keyVals
            if allGood
              then do
                PM.writeUnliftedArray entropies ix entropy
                for_ keyVals $ \(key,val) -> do
                  let j = fromIntegral @Word @Int (rem (fromIntegral @Word32 @Word (Hash.bytes entropy key)) (i2w count))
                  PM.writeSmallArray used j True
                  PM.writeUnliftedArray keys j (Bytes.toByteArray key)
                  PM.writeSmallArray values j val
                goB zs
              else case counter of
                0 -> throwIO $ HashMapException count
                  (map fst keyVals)
                  ((fmap.fmap.fmap) fst groups)
                _ -> goC (counter - 1) ix keyVals entropySz zs
      goB groups
      vals' <- PM.unsafeFreezeSmallArray values
      keys' <- PM.unsafeFreezeUnliftedArray keys
      entropies' <- PM.unsafeFreezeUnliftedArray entropies
      pure (Map entropyA entropies' keys' vals')
  where
  -- Combine duplicates upfront.
  xs' :: [(Bytes,v)]
  xs' = map
    (\rs ->
      ( unsafeHeadFst rs
      , List.foldl1' combine (map snd rs)
      )
    ) (List.groupBy (\(x,_) (y,_) -> x == y) (List.sortOn fst xs))
  count = List.length @[] xs' :: Int

findInitialEntropy ::
     CryptHandle
  -> Int
  -> Int
  -> Int
  -> [(Bytes,v)]
  -> IO ByteArray
{-# SCC findInitialEntropy #-}
findInitialEntropy !h !maxLen' !count !allowedCollisions xs = go 40
  where 
  go :: Int -> IO ByteArray
  go !ix = do
    entropy <- askForEntropy h maxLen'
    let maxCollisions = List.foldl'
          (\acc zs -> max acc (List.length @[] zs))
          0
          (List.group
            (List.sort
              (map (\(b,_) -> rem (fromIntegral @Word32 @Word (Hash.bytes entropy b)) (i2w count)) xs)
            )
          )
    if maxCollisions <= allowedCollisions
      then pure entropy
      else case ix of
        0 -> throwIO (HashMapException (-1) [] [])
        _ -> go (ix - 1)

askForEntropy :: CryptHandle -> Int -> IO ByteArray
askForEntropy !h !n = do
  entropy <- hGetEntropy h n
  when (ByteString.length entropy /= n)
    (fail "bytehash: askForEntropy failed, blame entropy")
  dst <- PM.newByteArray n
  ByteString.unsafeUseAsCStringLen entropy $ \(ptr, len) -> do
    let !(PM.MutableByteArray primDst) = dst
    PM.copyPtrToMutablePrimArray (PM.MutablePrimArray primDst) 0 ptr len
  PM.unsafeFreezeByteArray dst
    
requiredEntropy :: Word -> Word
requiredEntropy n = 8 * n + 8

errorThunk :: a
errorThunk = error "Data.Bytes.HashMap: mistake"

unsafeHeadFst :: [(a,b)] -> a
unsafeHeadFst ((x,_) : _) = x
unsafeHeadFst [] = error "Data.Bytes.HashMap: bad use of unsafeHeadFst"

w2i :: Word -> Int
w2i = fromIntegral

i2w :: Int -> Word
i2w = fromIntegral

upW32 :: Word32 -> Word
upW32 = fromIntegral

bytesEqualsByteArray :: Bytes -> ByteArray -> Bool 
bytesEqualsByteArray (Bytes arr1 off1 len1) arr2
  | len1 /= PM.sizeofByteArray arr2 = False
  | otherwise = compareByteArrays arr1 off1 arr2 0 len1 == EQ

compareByteArrays :: ByteArray -> Int -> ByteArray -> Int -> Int -> Ordering
compareByteArrays (ByteArray ba1#) (I# off1#) (ByteArray ba2#) (I# off2#) (I# n#) =
  compare (I# (Exts.compareByteArrays# ba1# off1# ba2# off2# n#)) 0

data HashMapException = HashMapException !Int [Bytes] [[(Word,Bytes)]]
  deriving stock (Show,Eq)
  deriving anyclass (Exception)

-- debugPrint :: Show v => Map v -> IO ()
-- debugPrint (Map entropy entropies keys vals) = do
--   putStrLn ("Tier 1 Entropy: " ++ show entropy)
--   putStrLn "Tier 2 Entropies:"
--   PM.traverseUnliftedArray_ print entropies
--   putStrLn "Keys:"
--   PM.traverseUnliftedArray_ print keys
--   putStrLn "Values:"
--   for_ vals print 
