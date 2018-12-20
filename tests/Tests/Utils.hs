module Tests.Utils
  ( testGroupM
  ) where

import Test.Tasty

testGroupM :: (Monad m) => TestName -> [m TestTree] -> m TestTree
testGroupM n xs = testGroup n <$> sequence xs
