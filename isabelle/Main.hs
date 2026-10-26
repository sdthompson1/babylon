module Main where

import CodeExport
import MiniCPrint (print_program)
import MiniCExample (minic_examples)
import Str
import Control.Exception
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

-- Read a source file as raw bytes, one Char (0-255) per byte, with no
-- character-set decoding. (readFile would decode using the locale encoding,
-- producing code points above 255 that makeChar would then truncate.)
readBinaryFile :: FilePath -> IO Prelude.String
readBinaryFile path = openBinaryFile path ReadMode >>= hGetContents

fromIsabelleString :: [Str.Char] -> Prelude.String
fromIsabelleString = map unmakeChar

-- Convert a filename to a Babylon module name: strip any leading directory
-- components, then strip any suffix (e.g. "dir/Foo.b" becomes "Foo").
moduleName :: FilePath -> Prelude.String
moduleName path =
  let base = reverse (takeWhile (\c -> c /= '/' && c /= '\\') (reverse path))
  in takeWhile (/= '.') base

-- Parse a command line argument into (module name, filename). The argument
-- is either "Name=path", giving the module name explicitly (e.g.
-- "A.B.C=dir/C.b"), or just "path", in which case the name is derived
-- from the filename using moduleName.
parseArg :: Prelude.String -> (Prelude.String, FilePath)
parseArg arg =
  case break (== '=') arg of
    (name, '=' : path) -> (name, path)
    _ -> (moduleName arg, arg)

-- MiniC mode: "Main --minic NAME OUT.c [EXPECTED.txt]" prints the hand-written
-- MiniC program NAME (from minic_examples, e.g. "example") as C to OUT.c and,
-- if EXPECTED.txt is given, writes its documented stdout there (the text that
-- the lemmas of MiniCExample.thy check the MiniC interpreter against). See
-- isabelle/minic/DESIGN.md, section 11.
minicMain :: Prelude.String -> FilePath -> Maybe FilePath -> IO ()
minicMain name cPath expectedPath =
  case [ (prog, out) | (n, (prog, out)) <- minic_examples, fromIsabelleString n == name ] of
    [] -> do
      hPutStrLn stderr ("Main: unknown MiniC program " ++ name ++ "; known: "
                        ++ unwords [ fromIsabelleString n | (n, _) <- minic_examples ])
      exitWith (ExitFailure 1)
    ((prog, out) : _) -> do
      writeBinaryFile cPath (fromIsabelleString (print_program prog))
      case expectedPath of
        Nothing -> return ()
        Just path -> writeBinaryFile path (fromIsabelleString out)

writeBinaryFile :: FilePath -> Prelude.String -> IO ()
writeBinaryFile path text = do
  h <- openBinaryFile path WriteMode
  hPutStr h text
  hClose h

-- Exit status: 0 on success, 1 if compilation fails, 2 if no arguments were
-- supplied, 3 if an exception occurs (e.g. a file could not be read).
-- (Without the handler, GHC would exit with status 1 on an uncaught exception,
-- making it indistinguishable from a compilation failure.)
main :: IO ()
main = realMain `catch` handler
  where
    handler :: SomeException -> IO ()
    handler e = case fromException e of
      -- exitWith works by throwing an ExitCode exception; let it through.
      Just ec -> throwIO (ec :: ExitCode)
      Nothing -> do
        hPutStrLn stderr ("Main: " ++ displayException e)
        exitWith (ExitFailure 3)

realMain :: IO ()
realMain = do
  args <- getArgs
  case args of
    [] -> do
      hPutStrLn stderr "Usage: Main [Name=]<RootModule.b> [[Name=]<OtherModule.b> ...]"
      hPutStrLn stderr "   or: Main --minic <program> <out.c> [<expected-output.txt>]"
      exitWith (ExitFailure 2)
    ["--minic", name, cPath] -> minicMain name cPath Nothing
    ["--minic", name, cPath, expectedPath] -> minicMain name cPath (Just expectedPath)
    _ -> do
      let namedFiles = map parseArg args
      contents <- mapM (readBinaryFile . snd) namedFiles
      let modules = zipWith (\(n, _) c -> (toIsabelleString n,
                                           toIsabelleString c))
                            namedFiles contents
      case run_compiler modules of
        CR_Success -> putStrLn "Success"
        CR_Errors errs -> do
          mapM_ (hPutStrLn stderr . fromIsabelleString) errs
          exitWith (ExitFailure 1)
