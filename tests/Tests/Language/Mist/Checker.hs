module Tests.Language.Mist.Checker (checkerTests) where

import Test.Tasty
import Test.Tasty.HUnit

import Data.Either (isRight, isLeft)
import Text.Printf

import Tests.Utils
import Tests.SimpleTypes

import Language.Mist.Checker

noPred = Boolean True

toRBase :: Type -> RType Expr ()
toRBase typ = RBase (Bind "vv") typ noPred

shouldCheck result = assertBool (printf "did not type check: %s" (show result)) (isRight result)

shouldFail result = assertBool (printf "type checked but shouldn't: %s" (show result)) (isLeft result)

checkerTests = testGroup "Language.Mist.Checker"
  [ elaborationTests
  ]

elaborationTests = testGroup "elaborate"
  [
    testCase "let id : A -> A = λx.x in ()" $
    let result
          = elaborate (Let
                       (Bind "id")
                       (Check (RForall (TV "A") (toRBase $ (TVar $ TV "A") :=> (TVar $ TV "A"))))
                       (Lam (Bind "x") (Id "x"))
                       Unit)
    in shouldCheck result

  , testCase "λx.y" $
    let result = elaborate (Lam (Bind "x") (Id "y"))
    in shouldFail result

  , testCase "let id : (ASSUME A -> A) = () in ()" $
    let result
          = elaborate (Let
                       (Bind "id")
                       (Assume (RForall (TV "A") (toRBase $ (TVar $ TV "A") :=> (TVar $ TV "A"))))
                       Unit
                       Unit)
    in shouldCheck result

  , testGroup "let id : A -> A = λx.x in id 1" $
    let result@(Right (CLet
                       (AnnBind "id" _)
                       (CTAbs (TV "A") _) -- TODO: lambda
                        _
                       -- (CApp (CTApp (CId "id") TInt) (CNumber 1))
                      ))
          = elaborate (Let
                       (Bind "id")
                       (Check (RForall (TV "A") (toRBase $ (TVar $ TV "A") :=> (TVar $ TV "A"))))
                       (Lam (Bind "x") (Id "x"))
                       (App (Id "id") (Number 1)))
    in [ testCase "type checks" $ shouldCheck result
       ]
  ]
