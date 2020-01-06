import Data.Bytes (Bytes)
import Data.Bytes.Hash (entropy)
import Data.Primitive (ByteArray)
import Test.Tasty (defaultMain,testGroup,TestTree)
import Test.Tasty.HUnit (testCase,assertEqual,Assertion,(@=?))

import qualified Data.Bytes as Bytes
import qualified Data.Bytes.Hash as Hash

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "bytehash"
  [ testCase "A" (Hash.bytes entropy 32 fooBytesA @=? Hash.bytes entropy 32 fooBytesB)
  , testCase "B" (Hash.bytes entropy 32 fooBytesA @=? Hash.byteArray entropy 32 fooByteArray)
  , testCase "C" (Hash.bytes entropy 32 mediumBytesA @=? Hash.bytes entropy 32 mediumBytesB)
  , testCase "D" (Hash.bytes entropy 32 mediumBytesA @=? Hash.byteArray entropy 32 mediumByteArray)
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
