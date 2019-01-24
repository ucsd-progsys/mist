module Tests.Language.Mist.Checker (checkerTests) where

import Debug.Trace

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

(==>) :: Id -> Id -> Type
a ==> b = TVar (TV a) :=> TVar (TV b)

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
                       (Check (RForall (TV "A") (toRBase $ "A" ==> "A")))
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
                       (Assume (RForall (TV "A") (toRBase $ "A" ==> "A")))
                       Unit
                       Unit)
    in shouldCheck result

  , testGroup "let id : A -> A = λx.x in id 1" $
    let result@(Right (CLet
                       _
                       (CTAbs (TV "A") _)
                       (CApp (CTApp (CId "id") TInt) (CNumber 1))
                      ))
          = elaborate (Let
                       (Bind "id")
                       (Check (RForall (TV "A") (toRBase $ "A" ==> "A")))
                       (Lam (Bind "x") (Id "x"))
                       (App (Id "id") (Number 1)))
    in [ testCase "type checks" $ shouldCheck result
       ]

  , testGroup "assume id : A -> A = () in let map : (A -> B) -> A -> B = λf.λx.f x in map id 1" $
    let result@(Right (CLet
                       _
                       _
                       (CLet
                        _
                        (CTAbs (TV "A") (CTAbs (TV "B") _))
                        (CApp (CApp (CTApp (CTApp (CId "map") TInt) TInt)
                                    (CTApp (CId "id") TInt))
                              (CNumber 1)))))
          = elaborate (Let
                       (Bind "id")
                       (Assume (RForall (TV "A") (toRBase $ "A" ==> "A")))
                       Unit
                       (Let
                        (Bind "map")
                        (Check (RForall (TV "A") (RForall (TV "B") (toRBase $ ("A" ==> "B") :=> ("A" ==> "B")))))
                        (Lam (Bind "f") (Lam (Bind "x") (App (Id "f") (Id "x"))))
                        (App (App (Id "map") (Id "id")) (Number 1))))
    in [ testCase "type checks" $ shouldCheck result
       ]

  , testGroup "assume const : A -> Int = () in let map : (A -> B) -> A -> B = λf.λx.f x in map const ()" $
    let result@(Right (CLet
                       _
                       _
                       (CLet
                        _
                        (CTAbs (TV "A") (CTAbs (TV "B") _))
                        (CApp (CApp (CTApp (CTApp (CId "map") TUnit) TInt)
                                    (CTApp (CId "const") TUnit))
                              CUnit))))
          = elaborate (Let
                       (Bind "const")
                       (Assume (RForall (TV "A") (toRBase $ (TVar $ TV "A") :=> TInt)))
                       Unit
                       (Let
                        (Bind "map")
                        (Check (RForall (TV "A") (RForall (TV "B") (toRBase $ ("A" ==> "B") :=> ("A" ==> "B")))))
                        (Lam (Bind "f") (Lam (Bind "x") (App (Id "f") (Id "x"))))
                        (App (App (Id "map") (Id "const")) Unit)))
    in [ testCase "type checks" $ shouldCheck result
       ]
  ]
