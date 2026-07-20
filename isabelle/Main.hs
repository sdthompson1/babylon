module Main where

import CodeExport
import Str
import Data.Bits
import System.Environment
import System.Exit
import System.IO

-- Convert between Haskell Chars and the Isabelle-generated Str.Char
-- (which represents a character as 8 booleans, least significant bit first).

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

unmakeChar :: Str.Char -> Prelude.Char
unmakeChar (Char b0 b1 b2 b3 b4 b5 b6 b7) =
  toEnum $ sum [ if b then n else 0
               | (b, n) <- zip [b0, b1, b2, b3, b4, b5, b6, b7]
                               [1, 2, 4, 8, 16, 32, 64, 128] ]

toIsabelleString :: Prelude.String -> [Str.Char]
toIsabelleString = map makeChar

fromIsabelleString :: [Str.Char] -> Prelude.String
fromIsabelleString = map unmakeChar

-- Convert a filename to a Babylon module name: strip any leading directory
-- components, then strip any suffix (e.g. "dir/Foo.b" becomes "Foo").
moduleName :: FilePath -> Prelude.String
moduleName path =
  let base = reverse (takeWhile (\c -> c /= '/' && c /= '\\') (reverse path))
  in takeWhile (/= '.') base

main :: IO ()
main = do
  args <- getArgs
  case args of
    [] -> do
      hPutStrLn stderr "Usage: Main <RootModule.b> [<OtherModule.b> ...]"
      exitWith (ExitFailure 2)
    files -> do
      contents <- mapM readFile files
      let modules = zipWith (\f c -> (toIsabelleString (moduleName f),
                                      toIsabelleString c))
                            files contents
      case run_compiler modules of
        CR_Success -> putStrLn "Success"
        CR_Errors errs -> do
          mapM_ (hPutStrLn stderr . fromIsabelleString) errs
          exitWith (ExitFailure 1)
