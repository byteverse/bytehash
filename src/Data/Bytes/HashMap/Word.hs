{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE BinaryLiterals #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UnboxedSums #-}
{-# LANGUAGE UnboxedTuples #-}

-- | Implementation of static hash map data structure.
module Data.Bytes.HashMap.Word
  ( Map
  , lookup
  , fromList
  , fromListWith
  ) where

import Prelude hiding (lookup)

import Data.Ord (Down(Down))
import Control.Monad (when)
import Data.Bits ((.&.),complement)
import Data.Bytes.Types (Bytes(Bytes))
import Data.Foldable (for_,foldlM)
import Data.Primitive (ByteArray,ByteArray(..),PrimArray(..))
import Data.Primitive.SmallArray (SmallArray(..))
import GHC.Exts (Int(I#),SmallArray#,ByteArray#,ArrayArray#,Int#,Word#)
import GHC.Word (Word(W#))
import GHC.IO.Handle.Internals (ioe_EOF)
import System.IO (Handle)
import Data.Primitive.Unlifted.Array (UnliftedArray(..))

import qualified Data.Bytes as Bytes
import qualified Data.List as List
import qualified Data.Bytes.Hash as Hash
import qualified Data.Primitive as PM
import qualified Data.Primitive.Unlifted.Array as PM
import qualified GHC.Exts as Exts

-- | A static perfect hash table where the keys are byte arrays. This
--   table cannot be updated after its creation, but all lookups have
--   guaranteed O(1) worst-case cost. It consumes linear space. This
--   is an excellent candidate for use with compact regions.
data Map = Map
  !ByteArray -- top-level entropy
  !(UnliftedArray ByteArray) -- entropies
  !(UnliftedArray ByteArray) -- keys
  !(PrimArray Word) -- values

fromList :: Handle -> [(Bytes,Word)] -> IO Map
fromList h = fromListWith h const

lookup :: Bytes -> Map -> Maybe Word
{-# inline lookup #-}
lookup
  (Bytes (ByteArray keyArr) (I# keyOff) (I# keyLen))
  (Map (ByteArray entropyA) (UnliftedArray entropies) (UnliftedArray keys) (PrimArray vals)) =
    case lookup# (# keyArr,keyOff,keyLen #) (# entropyA,entropies,keys,vals #) of
      (# (# #) | #) -> Nothing
      (# | v #) -> Just (W# v)

lookup# ::
     (# ByteArray#, Int#, Int# #)
  -> (# ByteArray#, ArrayArray#, ArrayArray#, ByteArray# #)
  -> (# (# #) | Word# #)
{-# noinline lookup# #-}
lookup# (# keyArr#, keyOff#, keyLen# #) (# entropyA#, entropies#, keys#, vals# #)
  | sz == 0 = (# (# #) | #)
  | PM.sizeofByteArray entropyA < reqEntropy = (# (# #) | #)
  | entropyB <- PM.indexUnliftedArray entropies (w2i (unsafeRem (Hash.bytes entropyA key) (i2w sz))),
    PM.sizeofByteArray entropyB >= reqEntropy,
    ix <- w2i (unsafeRem (Hash.bytes entropyB key) (i2w sz)),
    bytesEqualsByteArray key (PM.indexUnliftedArray keys ix),
    W# v <- PM.indexPrimArray vals ix = (# | v #)
  | otherwise = (# (# #) | #)
  where
  sz = PM.sizeofUnliftedArray entropies
  reqEntropy = w2i (requiredEntropy (i2w (Bytes.length key)))
  key = Bytes (ByteArray keyArr#) (I# keyOff#) (I# keyLen#)
  entropyA = ByteArray entropyA#
  entropies = UnliftedArray entropies# :: UnliftedArray ByteArray
  keys = UnliftedArray keys# :: UnliftedArray ByteArray
  vals = PrimArray vals# :: PrimArray Word

unsafeRem :: Word -> Word -> Word
unsafeRem (W# a) (W# b) = W# (Exts.remWord# a b)

fromListWith ::
     Handle -- ^ Source of randomness (use @/dev/urandom@ if uncertain)
  -> (Word -> Word -> Word)
  -> [(Bytes,Word)]
  -> IO Map
fromListWith h combine xs
  | count == 0 = pure (Map mempty mempty mempty mempty)
  | otherwise = do
      let maxLen' = w2i $ requiredEntropy $ i2w $
            List.foldl' (\acc (b,_) -> max (Bytes.length b) acc) 0 xs'
          allowedCollisions = ceiling (sqrt (fromIntegral @Int @Double (count + 1))) :: Int
      entropyA <- findInitialEntropy h maxLen' count allowedCollisions xs'
      let groups :: [[(Word,(Bytes,Word))]]
          groups = List.sortOn (Down . List.length @[])
            (List.groupBy (\(x,_) (y,_) -> x == y)
              (List.sortOn fst
                (List.map
                  (\(b,v) -> (rem (Hash.bytes entropyA b) (i2w count), (b,v)))
                  xs'
                )
              )
            )
      used <- PM.newSmallArray count False
      keys <- PM.newUnliftedArray count (mempty :: ByteArray)
      values <- PM.newPrimArray count
      PM.setPrimArray values 0 count (0 :: Word)
      entropies <- PM.newUnliftedArray count (mempty :: ByteArray)
      let {-# SCC goB #-}
          goB [] = pure ()
          goB (x : ps) = do
            let ix = w2i (unsafeHeadFst x)
                keyVals = map snd x
                maxGroupLen = List.foldl' (\acc (b,_) -> max (Bytes.length b) acc) 0 keyVals
            goC ix keyVals (w2i (requiredEntropy (i2w maxGroupLen))) ps
          {-# SCC goC #-}
          goC :: Int -> [(Bytes,Word)] -> Int -> [[(Word,(Bytes,Word))]] -> IO ()
          goC ix keyVals entropySz zs = do
            entropy <- askForEntropy h entropySz
            tmpUsed <- PM.cloneSmallMutableArray used 0 count
            allGood <- foldlM
              (\good (key,_) -> if good
                then do
                  let j = fromIntegral @Word @Int (rem (Hash.bytes entropy key) (i2w count))
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
                  let j = fromIntegral @Word @Int (rem (Hash.bytes entropy key) (i2w count))
                  PM.writeSmallArray used j True
                  PM.writeUnliftedArray keys j (Bytes.toByteArray key)
                  PM.writePrimArray values j val
                goB zs
              else goC ix keyVals entropySz zs
      goB groups
      vals' <- PM.unsafeFreezePrimArray values
      keys' <- PM.unsafeFreezeUnliftedArray keys
      entropies' <- PM.unsafeFreezeUnliftedArray entropies
      pure (Map entropyA entropies' keys' vals')
  where
  -- Combine duplicates upfront.
  xs' :: [(Bytes,Word)]
  xs' = map
    (\rs ->
      ( unsafeHeadFst rs
      , List.foldl1' combine (map snd rs)
      )
    ) (List.groupBy (\(x,_) (y,_) -> x == y) (List.sortOn fst xs))
  count = List.length @[] xs' :: Int

findInitialEntropy :: Handle -> Int -> Int -> Int -> [(Bytes,Word)] -> IO ByteArray
{-# SCC findInitialEntropy #-}
findInitialEntropy h maxLen' count allowedCollisions xs = do
  entropy <- askForEntropy h maxLen'
  let maxCollisions = List.foldl'
        (\acc zs -> max acc (List.length @[] zs))
        0
        (List.group
          (List.sort
            (map (\(b,_) -> rem (Hash.bytes entropy b) (i2w count)) xs)
          )
        )
  if maxCollisions <= allowedCollisions
    then pure entropy
    else findInitialEntropy h maxLen' count allowedCollisions xs

askForEntropy :: Handle -> Int -> IO ByteArray
askForEntropy h !n = do
  entropy <- Bytes.hGet h n
  when (Bytes.length entropy /= n) ioe_EOF
  pure (Bytes.toByteArrayClone entropy)
    
requiredEntropy :: Word -> Word
requiredEntropy n = ((n - 1) .&. complement 0b111) + 16

errorThunk :: a
errorThunk = error "Data.Bytes.HashMap: mistake"

unsafeHeadFst :: [(a,b)] -> a
unsafeHeadFst ((x,_) : _) = x
unsafeHeadFst [] = error "Data.Bytes.HashMap: bad use of unsafeHeadFst"

w2i :: Word -> Int
w2i = fromIntegral

i2w :: Int -> Word
i2w = fromIntegral

bytesEqualsByteArray :: Bytes -> ByteArray -> Bool 
bytesEqualsByteArray (Bytes arr1 off1 len1) arr2
  | len1 /= PM.sizeofByteArray arr2 = False
  | otherwise = compareByteArrays arr1 off1 arr2 0 len1 == EQ

compareByteArrays :: ByteArray -> Int -> ByteArray -> Int -> Int -> Ordering
compareByteArrays (ByteArray ba1#) (I# off1#) (ByteArray ba2#) (I# off2#) (I# n#) =
  compare (I# (Exts.compareByteArrays# ba1# off1# ba2# off2# n#)) 0

-- debugPrint :: Map -> IO ()
-- debugPrint (Map entropy entropies keys vals) = do
--   putStrLn ("Tier 1 Entropy: " ++ show entropy)
--   putStrLn "Tier 2 Entropies:"
--   PM.traverseUnliftedArray_ print entropies
--   putStrLn "Keys:"
--   PM.traverseUnliftedArray_ print keys
--   putStrLn "Values:"
--   for_ vals print 
