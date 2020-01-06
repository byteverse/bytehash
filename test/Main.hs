import Control.Monad (forM_) 
import Data.Bytes (Bytes)
import Data.Bytes.Hash (entropy)
import Data.Primitive (ByteArray)
import Data.Word (Word8)
import Hedgehog (Property,Gen,property,forAll,(===),failure)
import Hedgehog.Gen (integral,word8,word)
import Hedgehog.Gen (shuffle,list,enumBounded,int,frequency,choice,element)
import Hedgehog.Range (Range,linear)
import Test.Tasty (defaultMain,testGroup,TestTree)
import Test.Tasty.HUnit (testCase,assertEqual,Assertion,(@=?))
import Test.Tasty.Hedgehog (testProperty)

import qualified Data.Bytes as Bytes
import qualified Data.Bytes.Hash as Hash
import qualified Data.Bytes.HashMap as BT
import qualified Data.List as List
import qualified GHC.Exts as Exts

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "bytehash"
  [ testCase "A" (Hash.bytes entropy fooBytesA @=? Hash.bytes entropy fooBytesB)
  , testCase "B" (Hash.bytes entropy fooBytesA @=? Hash.byteArray entropy fooByteArray)
  , testCase "C" (Hash.bytes entropy mediumBytesA @=? Hash.bytes entropy mediumBytesB)
  , testCase "D" (Hash.bytes entropy mediumBytesA @=? Hash.byteArray entropy mediumByteArray)
  , testGroup "Map"
    [ testProperty "lookup" byteTableLookupProp
    ]
  ]

fooByteArray :: ByteArray
fooByteArray = Bytes.toByteArray (Bytes.fromAsciiString "foo")

fooBytesA :: Bytes
fooBytesA = Bytes.unsafeDrop 1 (Bytes.fromAsciiString "xfoo")

fooBytesB :: Bytes
fooBytesB = Bytes.unsafeDrop 2 (Bytes.fromAsciiString "abfoo")

mediumByteArray :: ByteArray
mediumByteArray = Bytes.toByteArray $ Bytes.fromAsciiString
  "abcdefghijklmnopqrstuvwxyz_now_i_know_my_abcs"

mediumBytesA :: Bytes
mediumBytesA = Bytes.unsafeDrop 1 $ Bytes.fromAsciiString
  "7abcdefghijklmnopqrstuvwxyz_now_i_know_my_abcs"

mediumBytesB :: Bytes
mediumBytesB = Bytes.unsafeDrop 2 $ Bytes.fromAsciiString
  "98abcdefghijklmnopqrstuvwxyz_now_i_know_my_abcs"

byteTableLookupProp :: Property
byteTableLookupProp = property $ do
  bytesList <- forAll $ list (linear 0 32) genBytes
  let pairs = map (\x -> (x,x)) bytesList
      table = BT.fromList pairs
  forM_ bytesList $ \bytes -> do
    BT.lookup bytes table === Just bytes

genBytes :: Gen Bytes
genBytes = do
  byteList <- list (linear 0 64) genByte
  front <- genOffset (List.length byteList)
  return (Bytes.unsafeDrop front (Exts.fromList byteList))

genByte :: Gen Word8
genByte = word8 (linear minBound maxBound)

genOffset :: Int -> Gen Int
genOffset originalLen = integral (linear 0 maxDiscard)
  where
  maxDiscard = min 19 (div originalLen 3)

