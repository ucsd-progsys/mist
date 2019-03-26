module Tests.Utils where

import Test.Tasty
import Test.Tasty.HUnit

import Language.Mist.UX (PPrint, pprint)

testGroupM :: (Monad m) => TestName -> [m TestTree] -> m TestTree
testGroupM n xs = testGroup n <$> sequence xs


(@/=?) :: (Eq a, Show a, HasCallStack) => a -> a -> Assertion
x @/=? y = (x /= y) @? msg
  where
    msg = "expected: " ++ show x ++ " /= " ++ show y ++ "\n but: " ++ show x ++ " == " ++ show y
