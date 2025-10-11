module Main where

import CodeExport
import Str
import Data.Bits
import System.IO
import System.Environment
import System.Exit
import qualified Data.ByteString as BS
import Data.Word
import Data.Binary.Get
import Control.Exception

makeChar :: Prelude.Char -> Str.Char
makeChar ch =
  let i = fromEnum ch
  in Char ((i .&. 1) /= 0)
     ((i .&. 2) /= 0)
     ((i .&. 4) /= 0)
     ((i .&. 8) /= 0)
     ((i .&. 16) /= 0)
     ((i .&. 32) /= 0)
     ((i .&. 64) /= 0)
     ((i .&. 128) /= 0)

readLength :: IO (Maybe Word32)
readLength = do
  result <- try $ BS.hGet stdin 4
  case result of
    Left (_ :: IOException) -> return Nothing
    Right bs -> if BS.length bs == 4
                then return $ Just $ runGet getWord32le (BS.fromStrict bs)
                else return Nothing

readContent :: Word32 -> IO (Maybe String)
readContent len = do
  result <- try $ BS.hGet stdin (fromIntegral len)
  case result of
    Left (_ :: IOException) -> return Nothing
    Right bs -> if BS.length bs == fromIntegral len
                then return $ Just $ map (toEnum . fromIntegral) $ BS.unpack bs
                else return Nothing

processFile :: String -> IO ()
processFile contents = do
  let str = map makeChar contents
  case run_compiler str of
    CR_Success -> BS.hPut stdout (BS.singleton 0)
    CR_LexError -> BS.hPut stdout (BS.singleton 1)
    CR_ParseError -> BS.hPut stdout (BS.singleton 2)
    CR_RenameError -> BS.hPut stdout (BS.singleton 3)
  hFlush stdout

mainLoop :: IO ()
mainLoop = do
  maybeLen <- readLength
  case maybeLen of
    Nothing -> return ()
    Just len -> do
      maybeContent <- readContent len
      case maybeContent of
        Nothing -> return ()
        Just content -> do
          processFile content
          mainLoop

main = do
  hSetBinaryMode stdin True
  hSetBinaryMode stdout True
  mainLoop
