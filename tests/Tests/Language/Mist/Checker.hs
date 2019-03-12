{-# LANGUAGE ScopedTypeVariables #-}
module Tests.Language.Mist.Checker (checkerTests) where

import Debug.Trace

import Test.Tasty
import Test.Tasty.HUnit

import Data.Either (isRight, isLeft)
import Text.Printf

import Tests.Utils
import Tests.SimpleTypes

import Language.Mist.Checker
import Language.Mist.UX (Result)

type ElabResult = Result (ElaboratedExpr (ElaboratedType () ()) ())

noPred = ()

toRBase :: Type -> RType () ()
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
                       (AnnBind "id" (ParsedCheck (RForall (TV "A") (toRBase $ "A" ==> "A"))))
                       (Lam (AnnBind "x" ParsedInfer) (Id "x"))
                       Unit)
    in shouldCheck result

  , testCase "λx.y" $
    let result :: ElabResult = elaborate (Lam (AnnBind "x" ParsedInfer) (Id "y"))
    in shouldFail result

  , testCase "let id : (ASSUME A -> A) = () in ()" $
    let result
          = elaborate (Let
                       (AnnBind "id" (ParsedAssume (RForall (TV "A") (toRBase $ "A" ==> "A"))))
                       Unit
                       Unit)
    in shouldCheck result

  , testGroup "let id : A -> A = λx.x in id 1" $
    let result@(Right (Let
                       _
                       (TAbs (TV "A") _)
                       (App (TApp (Id "id") TInt) (Number 1))))
          = elaborate (Let
                       (AnnBind "id" (ParsedCheck (RForall (TV "A") (toRBase $ "A" ==> "A"))))
                       (Lam (AnnBind "x" ParsedInfer) (Id "x"))
                       (App (Id "id") (Number 1)))
    in [ testCase "type checks" $ shouldCheck result
       ]

  , testGroup "assume id : A -> A = () in let map : (A -> B) -> A -> B = λf.λx.f x in map id 1" $
    let result@(Right (Let
                       _
                       _
                       (Let
                        _
                        (TAbs (TV "A") (TAbs (TV "B") _))
                         (App (App (TApp (TApp (Id "map") TInt) TInt)
                               (TApp (Id "id") TInt))
                           (Number 1)))))
          = elaborate (Let
                       (AnnBind "id" (ParsedAssume (RForall (TV "A") (toRBase $ "A" ==> "A"))))
                       Unit
                       (Let
                        (AnnBind "map" (ParsedCheck (RForall (TV "A") (RForall (TV "B") (toRBase $ ("A" ==> "B") :=> ("A" ==> "B"))))))
                        (Lam (AnnBind "f" ParsedInfer) (Lam (AnnBind "x" ParsedInfer) (App (Id "f") (Id "x"))))
                        (App (App (Id "map") (Id "id")) (Number 1))))
    in [ testCase "type checks" $ shouldCheck result
       ]

  , testGroup "assume const : A -> Int = () in let map : (A -> B) -> A -> B = λf.λx.f x in map const ()" $
    let result@(Right (Let
                       _
                       _
                       (Let
                        _
                        (TAbs (TV "A") (TAbs (TV "B") _))
                        (App (App (TApp (TApp (Id "map") TUnit) TInt)
                                    (TApp (Id "const") TUnit))
                              Unit))))
          = elaborate (Let
                       (AnnBind "const" (ParsedAssume (RForall (TV "A") (toRBase $ (TVar $ TV "A") :=> TInt))))
                       Unit
                       (Let
                        (AnnBind "map" (ParsedCheck (RForall (TV "A") (RForall (TV "B") (toRBase $ ("A" ==> "B") :=> ("A" ==> "B"))))))
                        (Lam (AnnBind "f" ParsedInfer) (Lam (AnnBind "x" ParsedInfer) (App (Id "f") (Id "x"))))
                        (App (App (Id "map") (Id "const")) Unit)))
    in [ testCase "type checks" $ shouldCheck result
       ]

  , testGroup "let id = λx.x in ()" $
    let result@(Right (Let
                       (AnnBind _ (ElabUnrefined (TForall (TV a1) (TVar (TV a2) :=> TVar (TV a3)))))
                       (TAbs (TV a4) _)
                       _))
          :: ElabResult
          = elaborate (Let
                       (AnnBind "id" ParsedInfer)
                       (Lam (AnnBind "x" ParsedInfer) (Id "x"))
                       Unit)
    in [ testCase "type checks" $ shouldCheck result
       , testCase "inferred type variables" $ do
           assertEqual "a1 == a2" a1 a2
           assertEqual "a2 == a3" a2 a3
           assertEqual "a3 == a4" a3 a4
       ]
  ]
