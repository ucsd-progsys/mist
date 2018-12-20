module Tests.Utils where

import Test.Tasty
import Test.Tasty.HUnit

testGroupM :: (Monad m) => TestName -> [m TestTree] -> m TestTree
testGroupM n xs = testGroup n <$> sequence xs


(@/=?) :: (Eq a, Show a, HasCallStack) => a -> a -> Assertion
x @/=? y = (x /= y) @? msg
  where
    msg = "expected: " ++ show x ++ " /= " ++ show y ++ "\n but: " ++ show x ++ " == " ++ show y
