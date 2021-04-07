module Tests.Integration.Tests (integrationTests) where

import Control.Exception
import Control.Monad
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
import Language.Mist.Config
import Language.Mist.UX (Result, SourceSpan, UserError)
import System.Console.CmdArgs.Verbosity

integrationTests = testGroupM "Integration"
  [ testGroup "pos" <$> dirTests "tests/pos" (mkTest mistSuccess)
  , testGroup "neg" <$> dirTests "tests/neg" (mkTest mistFailure)
  , testGroup "todo" <$> dirTests "tests/todo" crashTest
  ]

---------------------------------------------------------------------------
dirTests :: FilePath -> (FilePath -> TestName -> TestTree) -> IO [TestTree]
---------------------------------------------------------------------------
dirTests root testPred = do
  files    <- walkDirectory root
  let tests = [ rel | f <- files, isTest f, let rel = makeRelative root f ]
  return    $ testPred root <$> tests

isTest   :: FilePath -> Bool
isTest f = takeExtension f `elem` [".hs"]

---------------------------------------------------------------------------
mkTest :: (Result () -> IO ()) -> FilePath -> TestName -> TestTree
---------------------------------------------------------------------------
mkTest testPred dir file = testCase file $ do
  createDirectoryIfMissing True $ takeDirectory log
  withFile log WriteMode $ \h -> do
    setVerbosity Quiet
    ec <- runMist h (defConfig {srcFile = test})
    testPred ec
  where
    test = dir </> file
    log  = let (d, f) = splitFileName file in dir </> d </> ".liquid" </> f <.> "log"

data MistException = Success | Failure [UserError]
  deriving Show

instance Exception MistException

-- TODO abstract logging machinery, make tests fail when they don't crash
crashTest :: FilePath -> TestName -> TestTree
crashTest dir file = testCase file $ do
  createDirectoryIfMissing True $ takeDirectory log
  withFile log WriteMode $ \h -> (do
    ec <- (runMist h (defConfig {srcFile = test})) `catch` (\(SomeException _) -> pure $ Left [])
    case ec of
      Right _ -> throw Success
      Left errors -> throw $ Failure errors) `catch` handler
  where
    test = dir </> file
    log  = let (d, f) = splitFileName file in dir </> d </> ".liquid" </> f <.> "log"

    handler Success = assertFailure "expected failure but Mist succeeded"
    handler (Failure _) = pure ()

mistSuccess :: Result a -> Assertion
mistSuccess (Right _) = pure ()
mistSuccess (Left errors) = assertFailure (printf "expected success but got errors: %s" (show errors))

mistFailure :: Result a -> Assertion
mistFailure (Right _) = assertFailure "expected failure but Mist succeeded"
mistFailure (Left _) = pure ()

---------------------------------------------------------------------------
walkDirectory :: FilePath -> IO [FilePath]
---------------------------------------------------------------------------
walkDirectory root =
  fmap concat . traverse collect . candidates
    =<< (getDirectoryContents root `catchIOError` const (return []))
  where
    candidates fs = [root </> f | f <- fs, not (isExtSeparator (head f))]
    collect f = liftM3 bool (pure [f]) (walkDirectory f) (doesDirectoryExist f)
