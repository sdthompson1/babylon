module Main where

import CodeExport
import Str
import Data.Bits
import System.IO
import System.Environment
import System.Exit

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

main = do
  args <- getArgs
  withFile (args!!0) ReadMode $ \file -> do
    hSetEncoding file latin1
    contents <- hGetContents file
    let str = map makeChar contents
    if lex_test str then
      exitSuccess
    else
      exitWith (ExitFailure 1)  -- CR_LEX_ERROR
