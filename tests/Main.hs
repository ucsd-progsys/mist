{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Main (main) where

import Test.Tasty
import Test.Tasty.Ingredients.Rerun
import Test.Tasty.Runners
import Test.Tasty.Runners.AntXML

import Tests.Utils

import Tests.Integration.Tests
import Tests.Language.Mist.Names
import Tests.Language.Mist.Checker

main :: IO ()
main = runTests

runTests :: IO ()
runTests = run =<< testGroupM "Tests" [integrationTests, pure unitTests]
  where
    run = defaultMainWithIngredients [
                testRunner
            --  , includingOptions [ Option (Proxy :: Proxy NumThreads)
            --                     , Option (Proxy :: Proxy LiquidOpts)
            --                     , Option (Proxy :: Proxy SmtSolver) ]
              ]

unitTests = testGroup "Unit"
  [ namesTests
  , checkerTests
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
