{-# LANGUAGE ScopedTypeVariables #-}

module Language.Mist.Runner where

import Data.List                        (isInfixOf)
import Data.Char (toLower)
import Data.IORef
import Control.Exception

import Test.Tasty
import Test.Tasty.HUnit
import Text.Printf

import System.FilePath  --                 ((</>), (<.>))
import System.IO                        -- (withFile)
import System.Exit
import System.Environment (getArgs)

import Language.Mist.Utils
import Language.Mist.Normalizer
import Language.Mist.Types  hiding     (Result)
import Language.Mist.Parser
import Language.Mist.Compiler

-- import Debug.Trace (trace)

topMain:: IO ()
topMain = runCompiler `catch` esHandle stderr exitFailure

esHandle :: Handle -> IO a -> [UserError] -> IO a
esHandle h exitF es = renderErrors es >>= hPutStrLn h >> exitF

runCompiler :: IO ()
runCompiler = do
  f <- getSrcFile
  s <- readFile f
  let asm = compiler f s
  putStrLn asm
  exitSuccess

getSrcFile :: IO Text
getSrcFile = do
  args <- getArgs
  case args of
    [f] -> return f
    _   -> error "Please run with a single file as input"

staticOccursError = staticError "Type error: occurs check fails"
staticTypeError   = staticError "Type error"
overflowError     = Left "Error: arithmetic overflow"
rLines            = Right . unlines
dynamicError t    = Left ("Error: expected a " ++ pprint t)
staticError       = Left

-------------------------------------------------------------------------------
exec :: Text -> IO ()
--------------------------------------------------------------------------------
exec src = (putStrLn . either id id) =<< run "exec_tmp" (Code src)

--------------------------------------------------------------------------------
run :: FilePath -> Program -> IO Result
--------------------------------------------------------------------------------
run name pgm = do
  _ <- generateSource name pgm                -- generate source file
  _ <- generateAsm name `catch` esH           -- generate asm
  r <- executeShellCommand logF cmd timeLimit -- compile & run
  readResult resF logF r
  where
    cmd     = printf "make %s"     resF
    resF    = dirExt "output" name Res
    logF    = dirExt "output" name Log
    esH es  = withFile logF AppendMode $ \h ->
                esHandle h (return ()) es

-- | `timeLimit` for each test is 15 seconds
timeLimit :: Int
timeLimit = 15 * (10 ^ 6)

--------------------------------------------------------------------------------
generateAsm :: FilePath -> IO ()
--------------------------------------------------------------------------------
generateAsm name = do
  s      <- readFile srcF
  let asm = compiler srcF s
  writeFile asmF asm
  where
    srcF = dirExt "input"  name Src
    asmF = dirExt "output" name Asm

--------------------------------------------------------------------------------
generateSource :: FilePath -> Program -> IO ()
--------------------------------------------------------------------------------
generateSource _    File       = return ()
generateSource name (Code pgm) = writeFile srcF pgm
  where
    srcF                       = dirExt "input"  name Src

{-
forceWriteFile :: FilePath -> Text -> IO ()
forceWriteFile f s = withFile f WriteMode $ \h -> do
  hPutStr h s
  hClose h
-}

--------------------------------------------------------------------------------
readResult :: FilePath -> FilePath -> ExitCode -> IO Result
--------------------------------------------------------------------------------
readResult resF _     ExitSuccess      = Right <$> readFile resF
readResult _    _    (ExitFailure 100) = Left  <$> return "TIMEOUT!"
readResult _    logF (ExitFailure _  ) = Left  <$> readFile logF

dirExt :: FilePath -> FilePath -> Ext -> FilePath
dirExt dir name e = "tests" </> dir </> name `ext` e

--------------------------------------------------------------------------------
-- | A test program is either a filename or a text representation of source
--------------------------------------------------------------------------------
data Program = File | Code Text
type Result  = Either Text Text

--------------------------------------------------------------------------------
-- | Construct a single compiler test case from a `Program`
--------------------------------------------------------------------------------
mkTest :: Score -> String -> Program -> Result -> TestTree
mkTest sc name pgm = mkTest' sc 1 name (run name pgm)

mkTest' :: Score -> Int -> String -> IO Result -> Result -> TestTree
mkTest' sc n name act expect = testCase name $ do
  updateTotal sc n
  res <- act
  check sc n res expect

anfTest :: Score -> String -> Text -> Text -> TestTree
anfTest sc name inS expS = mkTest' sc 1 name (return $ anfRun inS) (Right expS)

anfRun :: Text -> Result
anfRun = Right . pprint . anormal . parse ""


--------------------------------------------------------------------------------
scoreTest' :: (Show b, Eq b) => Score -> (a -> b, a, b, Int, String) -> TestTree
--------------------------------------------------------------------------------
scoreTest' sc (f, x, expR, points, name) =
  testCase name $ do
    updateTotal sc points
    if f x == expR
      then updateCurrent sc points
      else assertFailure "Wrong Result"

-- check :: Result -> Result -> TestTree
check sc n (Right resV) (Right expectV)
  | trim expectV == trim resV          = updateCurrent sc n
  | otherwise                          = assertFailure "Wrong result"
check sc n (Left resE)  (Left  expectE)
  | matchError expectE resE            = updateCurrent sc n
  | otherwise                          = assertFailure "Wrong error"

check _ _ (Left resE)  (Right expectV) = assertEqual "Unexpected error"   ("Value " ++ expectV) ("Error " ++ resE)
check _ _ (Right resV) (Left  expectE) = assertEqual "Unexpected result"  ("Error " ++ expectE) ("Value " ++ resV)

matchError expectE resE = tx expectE `isInfixOf` tx resE
  where
      tx = map toLower
--------------------------------------------------------------------------------
type Score = IORef (Int, Int)
--------------------------------------------------------------------------------

getTotal :: Score -> IO (Int, Int)
getTotal = readIORef

updateTotal :: Score -> Int -> IO ()
updateTotal sc n = modifyIORef sc (\(x, y) -> (x, y + n))

updateCurrent :: Score -> Int -> IO ()
updateCurrent sc n = modifyIORef sc (\(x, y) -> (x + n, y))

initScore :: IO Score
initScore = newIORef (0, 0)
