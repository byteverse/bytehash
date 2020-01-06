{-# language BangPatterns #-}
{-# language MagicHash #-}

-- | Hash functions for byte sequences of a bounded size.
module Data.Bytes.Hash
  ( byteArray
  , bytes
  , entropy
  ) where

import Data.Bytes.Types (Bytes(Bytes))
import Data.Void (Void)
import GHC.Exts (Ptr(Ptr))
import Data.Word (Word64)
import Data.Primitive (ByteArray,sizeofByteArray)
import Data.Bits ((.&.),complement,unsafeShiftL)
import Data.Primitive.Ptr (indexOffPtr)
import Foreign.Ptr (castPtr)

import Data.Primitive.ByteArray.BigEndian (indexByteArray,indexUnalignedByteArray)

-- | Hash a byte sequence.
bytes ::
     Ptr Void -- ^ Entropy, should be an @Addr#@ literal
  -> Int -- ^ Number of 64-bit words of entropy
  -> Bytes -- ^ Bytes to hash
  -> Word64
bytes !addr !sz (Bytes arr off0 len0) = go (sz - 1) off0 len0 0 where
  -- The ptr index is in Word64 elements. The array index is in bytes.
  -- The remaining size is in bytes.
  go :: Int -> Int -> Int -> Word64 -> Word64
  go !ixPtr !ixArr !szB !acc = if szB >= 8
    then go
      (ixPtr - 1)
      (ixArr + 8)
      (szB - 8)
      (acc + ((indexOffPtr (castPtr addr) ixPtr :: Word64) * (indexUnalignedByteArray arr ixArr :: Word64)))
    else acc + 
      ( (indexOffPtr (castPtr addr) ixPtr :: Word64) *
        ((indexUnalignedByteArray arr ixArr :: Word64) .&. (complement ((unsafeShiftL 1 (szB * 8)) - 1)))
      )

-- | Hash a byte array. This takes advantage of the machine-word alignment
-- guarantee that GHC provides for byte arrays.
byteArray ::
     Ptr Void -- ^ Entropy, should be an @Addr#@ literal
  -> Int -- ^ Number of 64-bit words of entropy
  -> ByteArray -- ^ Bytes to hash
  -> Word64
byteArray !addr !sz !b = go (sz - 1) 0 (sizeofByteArray b) 0 where
  -- The indices are in Word64 elements. The remaining size is in bytes.
  go :: Int -> Int -> Int -> Word64 -> Word64
  go !ixPtr !ixArr !szB !acc = if szB >= 8
    then go
      (ixPtr - 1)
      (ixArr + 1)
      (szB - 8)
      (acc + ((indexOffPtr (castPtr addr) ixPtr :: Word64) * (indexByteArray b ixArr :: Word64)))
    else acc + 
      ( (indexOffPtr (castPtr addr) ixPtr :: Word64) *
        ((indexByteArray b ixArr :: Word64) .&. (complement ((unsafeShiftL 1 (szB * 8)) - 1)))
      )

-- | Statically-defined source of entropy. Contains 256 bytes.
entropy :: Ptr Void
entropy = Ptr "\
\11b8d61da8e062d6db1dc67710feab1c\
\2331e4ce6958755b1fa3b72f734b002a\
\1655b7745f2f162a5b088d1da4fdaaf7\
\c12968e2750c2bc7cce778f5c0fe8088\
\9984bdb2c493550f789ad4194b1dc4ff\
\5047c9db2bde9810c308370819cc55a7\
\7488981676f42e1e4c584bba4a35e788\
\64ae5a806dffbdfa0698f11c5406487e\
\7435db7b6abb4cdf1888e7638f08123b\
\8f8d1d003bb1a257c757d3b57d11a33f\
\dffe33f2bdcbac67250b6aa361d35f73\
\8d6dcaf7f25f2db137098049d7ecaf34\
\fa67b5d8820dadd05a63435acd56106e\
\6989f6c4337514558aeee378ee38eb05\
\8f5e1e5dad76ad752085e21fb8d300bf\
\5b171e125559b159aa9e6da09090bc2d"#
