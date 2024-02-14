{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NumericUnderscores #-}

import Control.Concurrent (threadDelay)
import Control.Monad
import Data.Bytes (Bytes)
import System.IO

import qualified Data.Bytes as Bytes
import qualified Data.Bytes.HashMap as Map

main :: IO ()
main = do
  rand <- openBinaryFile "/dev/urandom" ReadMode
  forever $ do
    xs <- getSeveralBytes rand
    putStrLn "Generated these byte sequences:"
    mapM_ print xs
    hFlush stdout
    putStrLn "Generated this hash map:"
    Map.fromList rand (map (\x -> (x, x)) xs) >>= Map.debugPrint
    putStrLn ""
    hFlush stdout
    threadDelay 1_000_000

getSeveralBytes :: Handle -> IO [Bytes]
getSeveralBytes h =
  fmap Bytes.uncons (Bytes.hGet h 1) >>= \case
    Just (w, remaining) | Bytes.null remaining -> do
      let sizes = case mod w 5 of
            0 -> [3, 12, 4]
            1 -> [8, 11, 6, 2]
            2 -> [19, 3, 9, 7, 15]
            3 -> [4, 3, 9, 7, 11, 1, 6]
            _ -> [0, 6, 17, 8, 4]
      mapM (Bytes.hGet h) sizes
    _ -> fail "getSeveralBytes: mistake"
