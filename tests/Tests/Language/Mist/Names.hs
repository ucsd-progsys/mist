module Tests.Language.Mist.Names (namesTests) where

import Test.Tasty
import Test.Tasty.HUnit

import Tests.Utils
import Tests.SimpleTypes

import Language.Mist.Names

namesTests = testGroup "Language.Mist.Names"
  [ refreshTests
  ]

refreshTests = testGroup "refresh"
  [
    testCase "uniquify λx.x" $
    let (Lam (Bind x1) (Id x2)) = uniquify (Lam (Bind "x") (Id "x"))
    in x1 @=? x2

  , testGroup "uniquify λx.(λx.x)" $
    let (Lam (Bind x1) (Lam (Bind x2) (Id x3))) =
          uniquify (Lam (Bind "x") (Lam (Bind "x") (Id "x")))
    in [ testCase "λ_.(λx2.x2)" $ x2 @=? x3
       , testCase "λx1.(λx2._)" $ x1 @/=? x2
       , testCase "λx1.(λ_.x2)" $ x1 @/=? x3
       ]
  ]
