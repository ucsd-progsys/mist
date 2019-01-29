-- | This module generates refinement type constraints
-- | (see Cosman and Jhala, ICFP '17)

{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections #-}
-- Extensions only needed for (Show (CG a e)) (for debugging)
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

module Language.Mist.CGen
  (
    generateConstraints

  , CGEnv
  , CGInfo (..)
  , SubC (..)
  ) where

-- TODO: Do we need to run a Uniqify pass before we run this module?
-- Matt: We should uniquify at the beginning and then maintain the unique names property

import           Language.Mist.Types
import           Language.Mist.Names
import           Language.Mist.Checker (primToUnpoly)

-------------------------------------------------------------------------------
-- Data Structures
-------------------------------------------------------------------------------
-- TODO: Break up function types, st these are only RRTy or RBase
-- | SubC Γ α β is the constraint  Γ |- α <: β
data SubC a = SAll Id (RType Core a) (SubC a) | SAnd (SubC a) (SubC a) | SHead (Core a)
  deriving (Show, Functor)

instance Boolable (SubC a) a where
  true a = SHead (true a)
  false a = SHead (false a)

type CGEnv a = [(Id, RType Core a)]
newtype CGInfo a = CGInfo { subCs :: [SubC a] }
  deriving Show

subC :: RType Core a -> RType Core a -> SubC a
subC (RFun (Bind x l) s s') (RFun (Bind y _) t t') =
    SAnd (subC t s)
         (SAll y t (subC (subst1 (CId y l) x s') t'))
 -- check the base types?
subC rtin@(RBase (Bind x l) _ _) (RBase (Bind y _) _ rout) =
    SAll x rtin (SHead $ subst1 (CId x l) y rout)
subC (RRTy _tin1 _tin2 _tin3) (RRTy _tout1 _tout2 _tout3) = undefined
-- TODO: polymorphism
subC (RForall _tin1 _tin2) (RForall _tout1 _tout2) = undefined
subC _ _ = undefined

freshKV :: a -> Type -> Fresh (RType Core a)
freshKV l = fresh l []

fresh :: a -> [(Id, Type)] -> Type -> Fresh (RType Core a)
fresh l γ (tau1 :=> tau2) = do
  t1 <- fresh l γ tau1
  x <- refreshId "karg#"
  t2 <- fresh l ((x,tau1):γ) tau2
  pure $ RFun (Bind x l) t1 t2

-- TODO : polymorphism
fresh _l _γ (TForall _tau1 _tau2) = undefined
fresh _l _γ (TVar _tau) = undefined

fresh l γ b = do
  vv <- Bind <$> refreshId "kVV#" <*> pure l
  k <- refreshId "k$"
  -- TODO: use actual ids from γ (see coreToFixpoint KVar)
  let vs = (`CId` l) . (k ++) . show <$> (zipWith const [1..] γ)
  pure $ RBase vv b (KVar k vs l)

-------------------------------------------------------------------------------
-- | generateConstraints is our main entrypoint to this module
-------------------------------------------------------------------------------
generateConstraints :: Core a -> SubC a
generateConstraints = fst . runFresh . synth []

-- run doctests with
--    stack build --copy-compiler-tool doctest
--    stack exec -- doctest -ilib lib/Language/Mist/CGen.hs
instance Show a => Show (Fresh a) where
    show = show . runFresh

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

synth :: CGEnv a -> Core a -> Fresh (SubC a, RType Core a)
-- Constants
synth _ e@(CUnit l)       = (true l,) <$> prim e TUnit
synth _ e@(CNumber  _ l)  = (true l,) <$> prim e TInt
synth _ e@(CBoolean _ l)  = (true l,) <$> prim e TBool
--- is this right? Shouldn't this be a lookup or something?
synth _ e@(CPrim2 o _ _ l) = (true l,) <$> prim e (primToUnpoly o)

-- vars, abstraction, application, let
synth γ (CId x l) = (true l,) <$> single γ x

-- The case where x has no annotation is slightly more complex. Read the
-- second equation first.
synth γ (CLam (AnnBind x (RUnrefined tau) l) e _)
  = do tHat <- freshKV l tau
       fmap (bindsRType (AnnBind x tHat l)) <$> synth ((x,tHat):γ) e
synth γ (CLam b@(AnnBind x t _l) e _)
  = fmap (bindsRType b) <$> synth ((x,t):γ) e

synth γ (CApp f y _) = do
  (c, RFun x t t') <- synth γ f
  (_, ty) <- synth γ y
  let cy = subC ty t
  pure (SAnd c cy, subst1 y (bindId x) t')

synth γ (CLet (AnnBind x (RUnrefined _) _) e1 e2 l)
  = do (c1, t1) <- synth γ e1
       (c2, t2) <- synth ((x,t1):γ) e2
       tHat <- freshKV l (eraseRType t2)
       pure (SAnd (SAnd c1 (subC t2 tHat)) (SAll x t1 c2), tHat)
synth γ (CLet (AnnBind x tx _) e1 e2 l)
  = do (c1, t1) <- synth γ e1
       (c2, t2) <- synth ((x,tx):γ) e2
       tHat <- freshKV l (eraseRType t2)
       pure (SAnd (SAnd (SAnd c1 (subC t1 tx)) (subC t2 tHat)) (SAll x tx c2), tHat)

-- Polymorphism
synth γ (CTAbs a e _) =
  fmap (RForall a) <$> synth γ e

synth γ (CTApp e tau l) = do
  -- if this blows up it's Checker's fault
  (c, RForall (TV a) t) <- synth γ e
  tHat <- freshKV l tau
  pure (c, subst1 tHat a t)

-- Fake ADT stuff
synth _γ (CTuple _e1 _e2 _) = undefined
synth _γ (CPrim _prim _)    = undefined
synth _γ (CIf _b _e1 _e2 _) = undefined

synth _ KVar{} = error "absurd"

prim :: Core a -> Type -> Fresh (RType Core a)
prim e t = do
  let l = extractC e
  vv <- refreshId "VV#"
  let reft = CPrim2 Equal (CId vv l) e l
  pure $ RBase (Bind vv l) t reft

single :: CGEnv a -> Id -> Fresh (RType Core a)
single γ x = case lookup x γ of
  Just rt@(RBase (Bind v l) _ _)
  -- `x` is already bound, so instead of "re-binding" x we should selfify
  -- (al la Ou et al. IFIP TCS '04)
   | v == x -> do v' <- refreshId "VV#"
                  let rt' = subst1 (CId v' l) x rt
                  pure $ strengthen (CPrim2 Equal (CId v' l) (CId x l) l) rt'
  Just rt -> pure rt
  Nothing -> error $ "Unbound Variable " ++ show x
