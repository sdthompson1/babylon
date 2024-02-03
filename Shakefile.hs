import Data.Char
import Development.Shake
import Development.Shake.Command
import Development.Shake.FilePath
import Development.Shake.Util


normalFlags = ["-g"]
optFlags = ["-O3"]
covFlags = normalFlags ++ ["--coverage"]
asanFlags = normalFlags ++ ["-fsanitize=address"]
profFlags = normalFlags ++ ["-O3", "-g", "-pg"]

getFlags = do
  mode <- getEnv "MODE"
  case mode of
    Nothing -> return normalFlags
    Just m -> do
      case map toUpper m of
        "OPT" -> return optFlags
        "COV" -> return covFlags
        "ASAN" -> return asanFlags
        "PROF" -> return profFlags
        _ -> return normalFlags


main :: IO ()
main = shakeArgs shakeOptions{shakeFiles="build"} $ do
    want ["build/babylon" <.> exe]

    phony "clean" $ do
        putInfo "Cleaning files in build"
        removeFilesAfter "build" ["//*"]

    -- Link Step
    "build/babylon" <.> exe %> \out -> do
        cs <- getDirectoryFiles "" ["src//*.c"]
        ss <- getDirectoryFiles "" ["src//*.s"]
        let os = ["build" </> c -<.> ".o" | c <- cs]
        need os

        flags <- getFlags
        cmd_ "gcc" flags "-o" [out] os ["-lsqlite3"]

    -- Compile Step
    "build//*.o" %> \out -> do
        let c = dropDirectory1 $ out -<.> "c"
        let m = out -<.> "m"

        let warnings = "-std=c11 -pedantic -Wall -Wextra -Wno-unused-parameter -Werror"
        flags <- getFlags

        cmd_ (WithStderr False) "gcc -fdiagnostics-color=always" flags warnings "-c" [c] "-o" [out] "-MMD -MF" [m]
        neededMakefileDependencies m
