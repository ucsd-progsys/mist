module Tests.Integration.Tests (integrationTests) where

import Control.Monad (liftM3)
import Data.Bool (bool)

import System.Directory
import System.Exit
import System.FilePath
import System.IO.Error
import System.IO

import Text.Printf

import Test.Tasty
import Test.Tasty.HUnit

import Tests.Utils

import Language.Mist.Runner
import Language.Mist.UX (Result, SourceSpan)

integrationTests = testGroupM "Integration"
  [ testGroup "pos" <$> dirTests "tests/Tests/Integration/pos" mistSuccess
  , testGroup "neg" <$> dirTests "tests/Tests/Integration/neg" mistFailure
  ]

---------------------------------------------------------------------------
-- dirTests :: FilePath -> (Result (Core SourceSpan) -> Assertion) -> IO [TestTree]
---------------------------------------------------------------------------
dirTests root testPred = do
  files    <- walkDirectory root
  let tests = [ rel | f <- files, isTest f, let rel = makeRelative root f ]
  return    $ mkTest testPred root <$> tests

isTest   :: FilePath -> Bool
isTest f = takeExtension f `elem` [".hs"]

---------------------------------------------------------------------------
-- mkTest :: (Result (Core SourceSpan) -> Assertion) -> FilePath -> FilePath -> TestTree
---------------------------------------------------------------------------
mkTest testPred dir file = testCase file $ do
  createDirectoryIfMissing True $ takeDirectory log
  withFile log WriteMode $ \h -> do
    ec <- runMist h test
    testPred ec
  where
    test = dir </> file
    log  = let (d, f) = splitFileName file in dir </> d </> ".liquid" </> f <.> "log"

mistSuccess :: Result a -> Assertion
mistSuccess (Right _) = pure ()
mistSuccess (Left errors) = assertFailure (printf "expected success but got errors: %s" (show errors))

mistFailure :: Result a -> Assertion
mistFailure (Right _) = assertFailure "expected failure but Mist succeeded"
mistFailure (Left _) = pure ()

----------------------------------------------------------------------------------------
walkDirectory :: FilePath -> IO [FilePath]
----------------------------------------------------------------------------------------
walkDirectory root =
  fmap concat . traverse collect . candidates
    =<< (getDirectoryContents root `catchIOError` const (return []))
  where
    candidates fs = [root </> f | f <- fs, not (isExtSeparator (head f))]
    collect f = liftM3 bool (pure [f]) (walkDirectory f) (doesDirectoryExist f)
