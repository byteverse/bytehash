{-# language BangPatterns #-}
{-# language MagicHash #-}
{-# language TypeApplications #-}

-- | Hash functions for byte sequences of a bounded size.
module Data.Bytes.Hash
  ( byteArray
  , bytes
  , entropy
  ) where

-- Implementation Notes
--
-- We use the length as the initial accumulator. This prevents byte
-- sequences of null bytes from hashing to the same value.
--
-- We perform a byte swap at the end. Technically, you are supposed to
-- perform a division at the end to throw away some of the lower bits.
-- This accomplishes something similar (preferring the upper bits).
--
-- We effectively pad all byte sequences with zeroes on the right-hand
-- side. This means we can terminate early once we run out of bytes
-- since all remaining additions would just be zero. We use a little-endian
-- interpretation of the underlying bytes along with some clever bit-shifting
-- to handle the incomplete machine word at the end of the byte sequence.
-- We read past the end of the array, but we zero out the invalid bytes
-- with conjunction. 

import Data.Bits ((.&.),unsafeShiftL)
import Data.Bytes.Types (Bytes(Bytes))
import Data.Primitive (ByteArray,sizeofByteArray)
import Data.Primitive.ByteArray.LittleEndian (indexByteArray,indexUnalignedByteArray)
import Data.Void (Void)
import Foreign.Storable (sizeOf)
import GHC.Exts (Ptr(Ptr))
import GHC.Word (Word(W#))

import qualified GHC.Exts as Exts

-- | Hash a byte sequence of length @n@.
bytes ::
     ByteArray -- ^ Entropy, must be at least @W + (⌈n / W⌉ * W)@ bytes
  -> Bytes -- ^ Bytes to hash
  -> Word
bytes !addr (Bytes arr off0 len0) =
  go 1 off0 len0 (indexByteArray addr 0 * fromIntegral @Int @Word (len0 + 1))
  where
  -- The ptr index is in Word64 elements. The array index is in bytes.
  -- The remaining size is in bytes.
  go :: Int -> Int -> Int -> Word -> Word
  go !ixPtr !ixArr !szB !acc = if szB >= wordSize
    then go
      (ixPtr + 1)
      (ixArr + wordSize)
      (szB - wordSize)
      (acc + ((indexByteArray addr ixPtr :: Word) * (indexUnalignedByteArray arr ixArr :: Word)))
    else byteSwap $ acc + 
      ( (indexByteArray addr ixPtr :: Word) *
        ((indexUnalignedByteArray arr ixArr :: Word) .&. ((unsafeShiftL 1 (szB * wordSize)) - 1))
      )

-- | Hash a byte array of length @n@. This takes advantage of the
-- machine-word alignment guarantee that GHC provides for byte arrays.
byteArray ::
     ByteArray -- ^ Entropy, must be at least @W + (⌈n / W⌉ * W)@ bytes
  -> ByteArray -- ^ Bytes to hash
  -> Word
byteArray !addr !b =
  go 1 0 sz (indexByteArray addr 0 * fromIntegral @Int @Word (sz + 1))
  where
  !sz = sizeofByteArray b
  -- The indices are in Word64 elements. The remaining size is in bytes.
  go :: Int -> Int -> Int -> Word -> Word
  go !ixPtr !ixArr !szB !acc = if szB >= wordSize
    then go
      (ixPtr + 1)
      (ixArr + 1)
      (szB - wordSize)
      (acc + ((indexByteArray addr ixPtr :: Word) * (indexByteArray b ixArr :: Word)))
    else byteSwap $ acc + 
      ( (indexByteArray addr ixPtr :: Word) *
        ((indexByteArray b ixArr :: Word) .&. ((unsafeShiftL 1 (szB * wordSize)) - 1))
      )

wordSize :: Int
wordSize = sizeOf (undefined :: Word)

byteSwap :: Word -> Word
{-# inline byteSwap #-}
byteSwap (W# w) = W# (Exts.byteSwap# w)

-- | Statically-defined source of entropy. Contains 256 bytes. All of these
-- bytes are odd numbers.
entropy :: Ptr Void
entropy = Ptr "\
\33fddd7b\
\9b1f3d5b\
\7dfff135\
\fdfffb1d\
\df779db5\
\ffb95bdb\
\1f39d73f\
\531bb959\
\59fbb13b\
\9d73db31\
\b591579b\
\99333357\
\f5d93f1f\
\7559b971\
\9fb7d5d1\
\f9915fdd\
\715f9b55\
\911f1b55\
\bdffb5b3\
\b577f177\
\7519fd7d\
\dbb75f79\
\319b399d\
\711f555d\
\bf997733\
\d133995d\
\17315171\
\15537d15\
\5f1f973d\
\15dbd5ff\
\db59f5b5\
\971f59f5\
\b5b11b73\
\377bbbfd\
\f9d5f951\
\31b3d71b\
\1bd19fd5\
\9f11dd13\
\157773b3\
\dd319791\
\5597d151\
\135f37fb\
\1511bd57\
\b97113f5\
\7719bd57\
\3d79795d\
\b9fdb937\
\7bfb3395\
\7539f1b3\
\7f1fd3f5\
\75bb799b\
\f13bbf39\
\37b7dd97\
\3951d3bf\
\73b15111\
\97b7fbd7\
\b35f3db7\
\b3b195d1\
\fd1b57b5\
\59d79df1\
\55dd13b9\
\7d1b3b75\
\b19f15dd\
\f13f31df"#
