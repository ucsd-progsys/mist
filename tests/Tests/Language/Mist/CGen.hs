{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeApplications #-}
module Tests.Language.Mist.CGen (cgenTests) where

import Test.Tasty
import Test.Tasty.HUnit

import Tests.Utils
import Tests.SimpleTypes

import Data.Bifunctor

import Language.Mist.Types (Predicate (..), MonadFresh (..), Constraint (..))
import qualified Language.Mist.Types as T
import Language.Mist.CGen
import Language.Mist.Names
import Language.Mist.Checker (primToUnpoly)

type P = Expr () ()

instance Predicate P where
  true = Boolean True
  false = Boolean False
  varsEqual x y = Prim2 Equal (Id x) (Id y)
  strengthen e1 e2 = Prim2 And e1 e2
  buildKvar x params = foldr (\arg kvar -> App kvar (Id arg)) (Id x) params
  varSubst x y e = subst1 @P @P (Id x) y e
  prim e@T.Unit{} = equalityPrim e TUnit
  prim e@T.Number{} = equalityPrim e TInt
  prim e@T.Boolean{} = equalityPrim e TBool
  prim e@(T.Prim2 op _ _ _) = equalityPrim e (primToUnpoly op)
  prim _ = error "prim on non primitive"

equalityPrim :: (MonadFresh m) => Expr t a -> Type -> m (RType P a)
equalityPrim e typ = do
  let loc = T.extract e
  vv <- refreshId $ "VV" ++ cSEPARATOR
  let e' = (second $ const ()) ((first $ const ()) e)
  pure $ T.RBase (T.Bind vv loc) typ (Prim2 Equal (Id vv) e')

cgenTests = testGroup "cgen"
  [
    testCase "()" $
    let cstrs = generateConstraints (Unit)
    in cstrs @?= Head (true @P)
  ]

-- $
-- >>> synth [] (CUnit ())
-- (SHead (CBoolean True ()),RBase (Bind {bindId = "VV###0", bindLabel = ()}) TUnit (CPrim2 Equal (CId "VV###0" ()) (CUnit ()) ()))
-- >>> synth [] (CNumber 1 ())
-- (SHead (CBoolean True ()),RBase (Bind {bindId = "VV###0", bindLabel = ()}) TInt (CPrim2 Equal (CId "VV###0" ()) (CNumber 1 ()) ()))
-- >>> let rInt = RBase (Bind "VV" ()) TInt (CBoolean True ())
-- >>> synth [] (CPrim2 Plus (CNumber 1 ()) (CNumber 2 ()) ())
-- (SHead (CBoolean True ()),RBase (Bind {bindId = "VV###0", bindLabel = ()}) TInt (CPrim2 Equal (CId "VV###0" ()) (CPrim2 Plus (CNumber 1 ()) (CNumber 2 ()) ()) ()))
-- >>> synth [] (CLam (AnnBind "x" rInt ()) (CId "x" ()) ())
-- (SHead (CBoolean True ()),RFun (Bind {bindId = "x", bindLabel = ()}) (RBase (Bind {bindId = "VV", bindLabel = ()}) TInt (CBoolean True ())) (RBase (Bind {bindId = "VV", bindLabel = ()}) TInt (CBoolean True ())))
-- >>> synth [] (CLet (AnnBind "y" rInt ()) (CUnit ()) (CApp (CLam (AnnBind "x" rInt ()) (CId "x" ()) ()) (CId "y" ()) ()) ())
-- (SAnd (SAnd (SAnd (SHead (CBoolean True ())) (SAll "VV###0" (RBase (Bind {bindId = "VV###0", bindLabel = ()}) TUnit (CPrim2 Equal (CId "VV###0" ()) (CUnit ()) ())) (SHead (CBoolean True ())))) (SAll "VV" (RBase (Bind {bindId = "VV", bindLabel = ()}) TInt (CBoolean True ())) (SHead (KVar "k$##2" [] ())))) (SAll "y" (RBase (Bind {bindId = "VV", bindLabel = ()}) TInt (CBoolean True ())) (SAnd (SHead (CBoolean True ())) (SAll "VV" (RBase (Bind {bindId = "VV", bindLabel = ()}) TInt (CBoolean True ())) (SHead (CBoolean True ()))))),RBase (Bind {bindId = "kVV###1", bindLabel = ()}) TInt (KVar "k$##2" [] ()))
-- >>> generateConstraints (CLet (AnnBind "y" rInt ()) (CUnit ()) (CApp (CLam (AnnBind "x" rInt ()) (CId "x" ()) ()) (CId "y" ()) ()) ())
-- SAnd (SAnd (SAnd (SHead (CBoolean True ())) (SAll "VV###0" (RBase (Bind {bindId = "VV###0", bindLabel = ()}) TUnit (CPrim2 Equal (CId "VV###0" ()) (CUnit ()) ())) (SHead (CBoolean True ())))) (SAll "VV" (RBase (Bind {bindId = "VV", bindLabel = ()}) TInt (CBoolean True ())) (SHead (KVar "k$##2" [] ())))) (SAll "y" (RBase (Bind {bindId = "VV", bindLabel = ()}) TInt (CBoolean True ())) (SAnd (SHead (CBoolean True ())) (SAll "VV" (RBase (Bind {bindId = "VV", bindLabel = ()}) TInt (CBoolean True ())) (SHead (CBoolean True ())))))
