module Utils
  ( testGroupM
  ) where

import Test.Tasty

testGroupM n xs = testGroup n <$> sequence xs
