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
    let (Lam (AnnBind x1 TInt) (Id x2)) = uniquify (Lam (AnnBind "x" TInt) (Id "x"))
    in x1 @=? x2

  , testGroup "uniquify λx.(λx.x)" $
    let (Lam (AnnBind x1 TInt) (Lam (AnnBind x2 TInt) (Id x3))) =
          uniquify (Lam (AnnBind "x" TInt) (Lam (AnnBind "x" TInt) (Id "x")))
    in [ testCase "λ_.(λx2.x2)" $ x2 @=? x3
       , testCase "λx1.(λx2._)" $ x1 @/=? x2
       , testCase "λx1.(λ_.x2)" $ x1 @/=? x3
       ]
  ]
