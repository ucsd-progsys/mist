{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PatternSynonyms #-}

module Tests.Language.Mist.Checker (checkerTests) where

import Test.Tasty
import Test.Tasty.HUnit

import Data.Either (isRight, isLeft)
import Text.Printf

import Tests.Utils ()
import Tests.SimpleTypes

import Language.Mist.Checker
import Language.Mist.UX (Result)


type ElabResult = Result (ElaboratedExpr (Expr () ()) ())

noPred = ()

toRBase :: Type -> RType () ()
toRBase typ = RBase (Bind "vv") typ noPred

(==>) :: Id -> Id -> Type
a ==> b = TVar (TV a) :=> TVar (TV b)

shouldCheck result = assertBool (printf "did not type check: %s" (show result)) (isRight result)

shouldFail result = assertBool (printf "type checked but shouldn't: %s" (show result)) (isLeft result)

checkerTests = testGroup "Language.Mist.Checker"
  [ elaborationTests
  , annotationTests
  ]

elaborationTests = testGroup "elaborate"
  [
    testCase "let id : A -> A = λx.x in ()" $
    let result = elaborate e1
    in shouldCheck result

  , testCase "λx.y" $
    let result :: ElabResult = elaborate (Lam (AnnBind "x" (Just ParsedInfer)) (Id "y"))
    in shouldFail result

  , testCase "let id : (ASSUME A -> A) = () in ()" $
    let result = elaborate e2
    in shouldCheck result

  , testGroup "let id : A -> A = λx.x in id 1" $
    let result@(Right (Let
                       _
                       (TAbs (TV "A") _)
                       (App (TApp (Id "id") TInt) (Number 1))))
          = elaborate e3
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
          = elaborate e4
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
          = elaborate e5
    in [ testCase "type checks" $ shouldCheck result
       ]

  , testGroup "let id = λx.x in ()" $
    let result@(Right (Let
                       (AnnBind _ (Just (ElabUnrefined (TForall (TV a1) (TVar (TV a2) :=> TVar (TV a3))))))
                       (TAbs (TV a4) _)
                       _))
          :: ElabResult
          = elaborate e6
    in [ testCase "type checks" $ shouldCheck result
       , testCase "inferred type variables" $ do
           assertEqual "a1 == a2" a1 a2
           assertEqual "a2 == a3" a2 a3
           assertEqual "a3 == a4" a3 a4
       ]
  ]

pattern A t = Just (ElabUnrefined t)

annotationTests = testGroup "annotation"
  [
    testCase "let id : A -> A = λx.x in ()" $ do
      let (Right elaborated) = elaborate e1
      let (AnnLet _
            (AnnTAbs _
              (AnnLam _
                (AnnId _ (A (TVar (TV "A"))))
                (A (TVar (TV "A") :=> TVar (TV "A"))))
              (A (TForall (TV "A") (TVar (TV "A") :=> TVar (TV "A")))))
            (AnnUnit (A TUnit))
            (A TUnit)) = annotate elaborated TUnit
      pure ()

  , testCase "let id : A -> A = λx.x in id 1" $ do
      let (Right elaborated) = elaborate e3
      let (AnnLet _
            (AnnTAbs _
              (AnnLam _
                (AnnId _ (A (TVar (TV "A"))))
                (A (TVar (TV "A") :=> TVar (TV "A"))))
              (A (TForall (TV "A") (TVar (TV "A") :=> TVar (TV "A")))))
            (AnnApp
             (AnnTApp (AnnId "id" (A (TForall (TV "A") (TVar (TV "A") :=> TVar (TV "A"))))) TInt (A (TInt :=> TInt)))
             (AnnNumber 1 (A TInt))
             (A TInt))
            (A TUnit)) = annotate elaborated TInt
      pure ()

  , testCase "assume id : A -> A = () in let map : (A -> B) -> A -> B = λf.λx.f x in map id 1" $ do
      let (Right elaborated) = elaborate e4
      let _ = annotate elaborated TInt
      pure ()

  , testCase "assume const : A -> Int = () in let map : (A -> B) -> A -> B = λf.λx.f x in map const ()" $ do
      let (Right elaborated) = elaborate e5
      let _ = annotate elaborated TUnit
      pure ()
  ]

-- | let id : A -> A = λx.x in ()
e1 = Let
     (AnnBind "id" (Just $ ParsedCheck (RForall (TV "A") (toRBase $ "A" ==> "A"))))
     (Lam (AnnBind "x" (Just ParsedInfer)) (Id "x"))
     Unit

-- | let id : (ASSUME A -> A) = () in ()
e2 = Let
     (AnnBind "id" (Just $ ParsedAssume (RForall (TV "A") (toRBase $ "A" ==> "A"))))
     Unit
     Unit

-- | let id : A -> A = λx.x in id 1
e3 = Let
     (AnnBind "id" (Just $ ParsedCheck (RForall (TV "A") (toRBase $ "A" ==> "A"))))
     (Lam (AnnBind "x" (Just ParsedInfer)) (Id "x"))
     (App (Id "id") (Number 1))

-- | assume id : A -> A = () in let map : (A -> B) -> A -> B = λf.λx.f x in map id 1
e4 = Let
     (AnnBind "id" (Just $ ParsedAssume (RForall (TV "A") (toRBase $ "A" ==> "A"))))
     Unit
     (Let
       (AnnBind "map" (Just $ ParsedCheck (RForall (TV "A") (RForall (TV "B") (toRBase $ ("A" ==> "B") :=> ("A" ==> "B"))))))
       (Lam (AnnBind "f" (Just ParsedInfer)) (Lam (AnnBind "x" (Just ParsedInfer)) (App (Id "f") (Id "x"))))
       (App (App (Id "map") (Id "id")) (Number 1)))

-- | assume const : A -> Int = () in let map : (A -> B) -> A -> B = λf.λx.f x in map const ()
e5 = Let
     (AnnBind "const" (Just $ ParsedAssume (RForall (TV "A") (toRBase $ (TVar $ TV "A") :=> TInt))))
     Unit
     (Let
       (AnnBind "map" (Just $ ParsedCheck (RForall (TV "A") (RForall (TV "B") (toRBase $ ("A" ==> "B") :=> ("A" ==> "B"))))))
       (Lam (AnnBind "f" (Just ParsedInfer)) (Lam (AnnBind "x" (Just ParsedInfer)) (App (Id "f") (Id "x"))))
       (App (App (Id "map") (Id "const")) Unit))

-- let id = λx.x in ()
e6 = Let
     (AnnBind "id" (Just ParsedInfer))
     (Lam (AnnBind "x" (Just ParsedInfer)) (Id "x"))
     Unit
