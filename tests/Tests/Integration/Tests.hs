module Tests.Integration.Tests (integrationTests) where

import Control.Monad (liftM3)
import Data.Bool (bool)

import System.Directory
import System.Exit
import System.FilePath
import System.IO.Error
import System.IO

import Test.Tasty
import Test.Tasty.HUnit

import Tests.Utils

import Language.Mist.Runner

integrationTests = testGroupM "Integration"
  [ testGroup "pos" <$> dirTests "tests/Integration/pos"    ExitSuccess
  , testGroup "neg" <$> dirTests "tests/Integration/neg"    (ExitFailure 1)
  ]


---------------------------------------------------------------------------
dirTests :: FilePath -> ExitCode -> IO [TestTree]
---------------------------------------------------------------------------
dirTests root code = do
  files    <- walkDirectory root
  let tests = [ rel | f <- files, isTest f, let rel = makeRelative root f ]
  return    $ mkTest code root <$> tests

isTest   :: FilePath -> Bool
isTest f = takeExtension f `elem` [".hs"]

---------------------------------------------------------------------------
mkTest :: ExitCode -> FilePath -> FilePath -> TestTree
---------------------------------------------------------------------------
mkTest code dir file = testCase file $ do
  createDirectoryIfMissing True $ takeDirectory log
  withFile log WriteMode $ \h -> do
    ec <- runMist h test
    assertEqual "Wrong exit code" code (resultExitCode ec)
  where
    test = dir </> file
    log  = let (d, f) = splitFileName file in dir </> d </> ".liquid" </> f <.> "log"

-- resultExitCode :: Result -> ExitCode
resultExitCode (Left _)  = ExitFailure 1
resultExitCode (Right _) = ExitSuccess

----------------------------------------------------------------------------------------
walkDirectory :: FilePath -> IO [FilePath]
----------------------------------------------------------------------------------------
walkDirectory root =
  fmap concat . traverse collect . candidates
    =<< (getDirectoryContents root `catchIOError` const (return []))
  where
    candidates fs = [root </> f | f <- fs, not (isExtSeparator (head f))]
    collect f = liftM3 bool (pure [f]) (walkDirectory f) (doesDirectoryExist f)
