{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Language.Mist.Test (runTests) where

import System.Directory
import System.Exit
import System.FilePath
import System.IO.Error
import System.IO

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.Ingredients.Rerun
import Test.Tasty.Runners
import Test.Tasty.Runners.AntXML

import Language.Mist.Runner 

runTests :: IO ()
runTests = run =<< group "Tests" [unitTests]
  where
    run = defaultMainWithIngredients [
                testRunner
            --  , includingOptions [ Option (Proxy :: Proxy NumThreads)
            --                     , Option (Proxy :: Proxy LiquidOpts)
            --                     , Option (Proxy :: Proxy SmtSolver) ]
              ]

testRunner :: Ingredient
testRunner = rerunningTests
               [ listingTests
               , combineReporters myConsoleReporter antXMLRunner
               , myConsoleReporter
               ]

myConsoleReporter :: Ingredient
myConsoleReporter = consoleTestReporter

-- | Combine two @TestReporter@s into one.
--
-- Runs the reporters in sequence, so it's best to start with the one
-- that will produce incremental output, e.g. 'consoleTestReporter'.
combineReporters :: Ingredient -> Ingredient -> Ingredient
combineReporters (TestReporter opts1 run1) (TestReporter opts2 run2)
  = TestReporter (opts1 ++ opts2) $ \opts tree -> do
      f1 <- run1 opts tree
      f2 <- run2 opts tree
      return $ \smap -> f1 smap >> f2 smap
combineReporters _ _ = error "combineReporters needs TestReporters"

unitTests = group "Unit" 
  [ testGroup "pos" <$> dirTests "tests/pos"    ExitSuccess
  , testGroup "neg" <$> dirTests "tests/neg"    (ExitFailure 1)
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

{- 
  mkTest testCmd code dir file
  = testCase file $
      if test `elem` knownToFail
      then do
        printf "%s is known to fail: SKIPPING" test
        assertEqual "" True True
      else do
        createDirectoryIfMissing True $ takeDirectory log
        bin <- binPath "fixpoint"
        withFile log WriteMode $ \h -> do
          let cmd     = testCmd bin dir file
          (_,_,_,ph) <- createProcess $ (shell cmd) {std_out = UseHandle h, std_err = UseHandle h}
          c          <- waitForProcess ph
          assertEqual "Wrong exit code" code c
-}




-- resultExitCode :: Result -> ExitCode 
resultExitCode (Left _)  = ExitFailure 1
resultExitCode (Right _) = ExitSuccess 

---------------------------------------------------------------------------
-- type TestCmd = FilePath -> FilePath -> FilePath -> String

----------------------------------------------------------------------------------------
-- Generic Helpers
----------------------------------------------------------------------------------------

group n xs = testGroup n <$> sequence xs

----------------------------------------------------------------------------------------
walkDirectory :: FilePath -> IO [FilePath]
----------------------------------------------------------------------------------------
walkDirectory root
  = do (ds,fs) <- partitionM doesDirectoryExist . candidates =<< (getDirectoryContents root `catchIOError` const (return []))
       (fs++) <$> concatMapM walkDirectory ds
  where
    candidates fs = [root </> f | f <- fs, not (isExtSeparator (head f))]

partitionM :: Monad m => (a -> m Bool) -> [a] -> m ([a],[a])
partitionM f = go [] []
  where
    go ls rs []     = return (ls,rs)
    go ls rs (x:xs) = do b <- f x
                         if b then go (x:ls) rs xs
                              else go ls (x:rs) xs

-- isDirectory :: FilePath -> IO Bool
-- isDirectory = fmap Posix.isDirectory . Posix.getFileStatus

concatMapM :: Applicative m => (a -> m [b]) -> [a] -> m [b]
concatMapM _ []     = pure []
concatMapM f (x:xs) = (++) <$> f x <*> concatMapM f xs
