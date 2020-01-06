{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UnboxedSums #-}
{-# LANGUAGE UnboxedTuples #-}

-- | Implementation of static hash map data structure.
module Data.Bytes.HashMap
  ( Map
  , lookup
  , fromList
  , fromListWith
  , toList
  ) where

import Prelude hiding (lookup)

import Control.Monad.ST (ST,runST)
import Data.Bits ((.&.),unsafeShiftL,countLeadingZeros,finiteBitSize)
import Data.Bytes.Types (Bytes(Bytes))
import Data.Monoid (Any(..))
import Data.Primitive (ByteArray,MutableArray,ByteArray(..))
import Data.Primitive.SmallArray (SmallArray(..))
import Foreign.Ptr (plusPtr)
import GHC.Exts (Int(I#),Int#,ByteArray#,SmallArray#,Ptr)
import Data.Void (Void)

import qualified Data.Bytes as B
import qualified Data.Bytes.Hash as Hash
import qualified Data.Primitive as PM
import qualified Data.Primitive.SmallArray as PMSA
import qualified Data.Semigroup as SG
import qualified GHC.Exts as Exts

-- | A static perfect hash table where the keys are byte arrays. This
--   table cannot be updated after its creation, but all lookups have
--   guaranteed O(1) worst-case cost. It consumes linear space. This
--   is an excellent candidate for use with compact regions.
--
--   Implementation details require keys to be less than 128 bytes.
newtype Map v = Map (SmallArray (Cell v))
-- invariant for Map: the Array must have a length
-- that is a power of two.

type Map# v = SmallArray# (Cell v)
type Bytes# = (# ByteArray#, Int#, Int# #)

data Cell v
  = CellZero
  | CellOne
      {-# UNPACK #-} !ByteArray -- payload
      !v -- value
  | CellMany
      {-# UNPACK #-} !(Ptr Void) -- beginning of entropy
      {-# UNPACK #-} !(SmallArray (Info v)) -- length must be power of two

data Info v
  = InfoAbsent
  | InfoPresent
      {-# UNPACK #-} !ByteArray -- payload
      !v

data TableBuilder s v = TableBuilder
  {-# UNPACK #-} !Int -- count of the total number of distinct ByteArrays
  {-# UNPACK #-} !(MutableArray s (ArrList v))

data ArrList v
  = ArrListCons !ByteArray !v !(ArrList v)
  | ArrListNil

-- Reconsider this. We should probably have a Semigroup constraint
-- on the element type.
instance Semigroup (Map v) where
  (<>) = append
  
instance Monoid (Map v) where
  mempty = empty
  mappend = (SG.<>)

empty :: Map v
empty = runST $ do
  -- i think we could use 1 instead of 2. We definitely
  -- cannot use 0.
  marr <- PMSA.newSmallArray 2 CellZero
  arr <- PMSA.unsafeFreezeSmallArray marr
  return (Map arr)

append :: Map v -> Map v -> Map v
append a b = fromList (toList a ++ toList b)

toList :: Map v -> [(Bytes,v)]
toList (Map arr) = foldMap cellToList arr

cellToList :: Cell v -> [(Bytes,v)]
cellToList = \case
  CellZero -> []
  CellOne barr v -> [(B.fromByteArray barr, v)]
  CellMany _ arr -> foldMap infoToList arr

infoToList :: Info v -> [(Bytes,v)]
infoToList = \case
  InfoAbsent -> []
  InfoPresent barr v -> [(B.fromByteArray barr, v)]

showArrList :: ArrList v -> String
showArrList = show . arrListToList

arrListToList :: ArrList v -> [ByteArray]
arrListToList ArrListNil = []
arrListToList (ArrListCons b _ xs) = b : arrListToList xs

emptyTableBuilder :: ST s (TableBuilder s v)
emptyTableBuilder = do
  marr <- PM.newArray 8 ArrListNil
  return (TableBuilder 0 marr)

lookup :: Bytes -> Map v -> Maybe v
{-# inline lookup #-}
lookup (Bytes (ByteArray arr) (I# off) (I# len)) (Map (SmallArray m)) =
  case lookup# (# arr, off, len #) m of
    (# (# #) | #) -> Nothing
    (# | val #) -> Just val

lookup# :: Bytes# -> Map# v -> (# (# #) | v #)
{-# noinline lookup# #-}
lookup# needle' m' = if B.length needle < 128
  then
    let !outerHash = remBase2Divisor
          (w2i (Hash.bytes Hash.entropy needle)) (PMSA.sizeofSmallArray sarrOuter) in
    case PMSA.indexSmallArray sarrOuter outerHash of
      CellZero -> (# (# #) | #)
      CellOne ba v -> if bytesEqualsByteArray needle ba
        then (# | v #)
        else (# (# #) | #)
      CellMany entropy sarrInner ->
        let !innerHash = remBase2Divisor
              (w2i (Hash.bytes entropy needle))
              (PMSA.sizeofSmallArray sarrInner) in
        case PMSA.indexSmallArray sarrInner innerHash of
          InfoAbsent -> (# (# #) | #)
          InfoPresent ba v -> if bytesEqualsByteArray needle ba
            then (# | v #)
            else (# (# #) | #)
  else (# (# #) | #)
  where
  needle = boxBytes needle'
  Map sarrOuter = boxMap m'

boxMap :: Map# v -> Map v
boxMap a = Map (SmallArray a)

boxBytes :: Bytes# -> Bytes
boxBytes (# arr, off, len #) = Bytes (ByteArray arr) (I# off) (I# len)

-- This calls freeze on the arrays inside of the builder,
-- so do not reuse it after calling this function.
freezeBuilder :: forall s v. TableBuilder s v -> ST s (Map v)
freezeBuilder (TableBuilder _ marr) = do
  msarr <- PMSA.newSmallArray (PM.sizeofMutableArray marr) CellZero
  let go :: Int -> ST s ()
      go !ix = if ix < PM.sizeofMutableArray marr
        then do
          arrList <- PM.readArray marr ix
          case arrList of
            ArrListNil -> return () -- already been set to CellZero
            ArrListCons b v ArrListNil -> do
              PMSA.writeSmallArray msarr ix (CellOne b v)
            ArrListCons _ _ (ArrListCons _ _ _) -> do
              (salt, sarr) <- buildCollisionless 0 arrList
              PMSA.writeSmallArray msarr ix (CellMany salt sarr)
          go (ix + 1)
        else return ()
  go 0
  sarr <- PMSA.unsafeFreezeSmallArray msarr
  return (Map sarr)

-- This function may fail if the salt collisions keep happening.
-- An attacker might cause this, but the odds of this occurring
-- naturally are nearly zero. Do not pass this function an ArrList
-- of length zero.
buildCollisionless :: Int -> ArrList v -> ST s (Ptr Void,SmallArray (Info v))
buildCollisionless !salt !arrList = if salt < 12
  then do
    let !arrLen = arrListLength arrList 
        !len = twoExp (truncLogBaseTwo (arrLen * arrLen))
    msarr <- PMSA.newSmallArray len InfoAbsent
    let entropy = plusPtr Hash.entropy (8 * salt)
    Any hasCollisions <- arrListForM_ arrList $ \b v -> do
      let !ix = remBase2Divisor (w2i (Hash.byteArray entropy b)) len
      x <- PMSA.readSmallArray msarr ix
      case x of
        InfoAbsent -> do
          PMSA.writeSmallArray msarr ix (InfoPresent b v)
          return (Any False)
        InfoPresent _ _ -> return (Any True)
    if hasCollisions
      then buildCollisionless (salt + 1) arrList
      else do
        sarr <- PMSA.unsafeFreezeSmallArray msarr
        return (entropy, sarr)
  else error
    ( "buildCollisionless: too many tries: " ++ showArrList arrList ++
     " length: " ++ show (arrListLength arrList)
    )

construct :: forall v c.
     (v -> v -> v)
  -> (forall s d. (Bytes -> v -> c -> d -> ST s d) -> c -> d -> ST s d)
  -> c 
  -> Map v
construct combine f c0 = runST $ do
  tb0 <- emptyTableBuilder
  tb <- microConstruct combine f c0 tb0
  freezeBuilder tb

microConstruct :: forall v c s.
     (v -> v -> v)
  -> ((Bytes -> v -> c -> TableBuilder s v -> ST s (TableBuilder s v)) -> c -> TableBuilder s v -> ST s (TableBuilder s v))
  -> c -> TableBuilder s v -> ST s (TableBuilder s v)
microConstruct combine f c0 tb0 = f (\b v c d -> do
    d' <- insertBuilder combine d (B.toByteArray b) v
    microConstruct combine f c d'
  ) c0 tb0

insertBuilder :: (v -> v -> v) -> TableBuilder s v -> ByteArray -> v -> ST s (TableBuilder s v)
insertBuilder combine (TableBuilder count marr0) key val =
  if PM.sizeofByteArray key < 128
    then do
      marr1 <- if count < PM.sizeofMutableArray marr0
        then return marr0
        else growBuilderArray combine marr0
      insertBuilderArray combine marr1 key val
      return (TableBuilder (count + 1) marr1)
    else error "Data.Bytes.HashMap: insertBuilder cannot handle keys with 128 or more bytes"
      
truncLogBaseTwo :: Int -> Int
truncLogBaseTwo n = finiteBitSize (undefined :: Int) - countLeadingZeros n - 1

twoExp :: Int -> Int
twoExp n = unsafeShiftL 1 n

growBuilderArray :: (v -> v -> v) -> MutableArray s (ArrList v) -> ST s (MutableArray s (ArrList v))
growBuilderArray combine marr = do
  marrBig <- PM.newArray (PM.sizeofMutableArray marr * 2) ArrListNil
  builderArrayForM_ marr $ \b v -> do
    -- even though we pass combine, it should actually
    -- never be used here since everything should already
    -- be unique.
    insertBuilderArray combine marrBig b v
  return marrBig
  
-- this function cannot resize the table
insertBuilderArray :: (v -> v -> v) -> MutableArray s (ArrList v) -> ByteArray -> v -> ST s ()
insertBuilderArray combine marr b v = do
  let theHash = remBase2Divisor (w2i (Hash.byteArray Hash.entropy b)) (PM.sizeofMutableArray marr)
  arrList <- PM.readArray marr theHash
  let newArrList = insertArrList combine b v arrList
  PM.writeArray marr theHash newArrList

insertArrList :: (v -> v -> v) -> ByteArray -> v -> ArrList v -> ArrList v
insertArrList _ b v ArrListNil = ArrListCons b v ArrListNil
insertArrList combine b v (ArrListCons b' v' xs) =
  if b == b'
    then ArrListCons b' (combine v v') xs
    else ArrListCons b' v' (insertArrList combine b v xs)

-- precondition: the divisor must be two raised to some power.
remBase2Divisor :: Int -> Int -> Int
remBase2Divisor quotient divisor = quotient .&. (divisor - 1)

builderArrayForM_ ::
     MutableArray s (ArrList v)
  -> (ByteArray -> v -> ST s ())
  -> ST s ()
builderArrayForM_ marr f = go (PM.sizeofMutableArray marr - 1) where
  go ix = if ix >= 0
    then do
      arrList <- PM.readArray marr ix
      arrListForM_ arrList f
      go (ix - 1)
    else return ()

-- expects a commutative monoid
arrListForM_ :: forall s a v.
     Monoid a
  => ArrList v
  -> (ByteArray -> v -> ST s a)
  -> ST s a
arrListForM_ arrList f = go arrList mempty
  where
  go :: ArrList v -> a -> ST s a
  go ArrListNil !a = return a
  go (ArrListCons b v xs) !a = do
    a' <- f b v
    go xs (mappend a a')

arrListLength :: forall v. ArrList v -> Int
arrListLength = go 0 where
  go :: Int -> ArrList v -> Int
  go !n ArrListNil = n
  go !n (ArrListCons _ _ xs) = go (n + 1) xs

fromList :: [(Bytes,v)] -> Map v
fromList = fromListWith const

fromListWith :: (v -> v -> v) -> [(Bytes,v)] -> Map v
fromListWith combine = construct combine (\f xs d -> case xs of
    [] -> return d
    (b,v) : ys -> f b v ys d
  )

w2i :: Word -> Int
w2i = fromIntegral

bytesEqualsByteArray :: Bytes -> ByteArray -> Bool 
bytesEqualsByteArray (Bytes arr1 off1 len1) arr2
  | len1 /= PM.sizeofByteArray arr2 = False
  | otherwise = compareByteArrays arr1 off1 arr2 0 len1 == EQ

compareByteArrays :: ByteArray -> Int -> ByteArray -> Int -> Int -> Ordering
compareByteArrays (ByteArray ba1#) (I# off1#) (ByteArray ba2#) (I# off2#) (I# n#) =
  compare (I# (Exts.compareByteArrays# ba1# off1# ba2# off2# n#)) 0
