-- | This module generates refinement type constraints
-- | (see Cosman and Jhala, ICFP '17)

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
import           Language.Mist.Checker (prim2Unpoly)
import           Control.Monad.State.Strict
-- import qualified Language.Fixpoint.Types as F

-------------------------------------------------------------------------------
-- Data Structures
-------------------------------------------------------------------------------

-- TODO: Break up function types, st these are only RRTy or RBase
-- | SubC Γ α β is the constraint  Γ |- α <: β
data SubC a = SubC (CGEnv a) (RType Core a) (RType Core a)
  deriving Show
newtype CGInfo a = CGInfo { subCs :: [SubC a] }
  deriving Show

-- | Constraint Generation Monad
type CG a = StateT (CGInfo a) Fresh
type CGEnv a = [(Id, RType Core a)]

instance MonadFresh (CG a) where
  refreshId = lift . refreshId
  popId     = lift popId
  lookupId  = lift . lookupId

instance Semigroup (CGInfo a) where
  CGInfo a <> CGInfo b = CGInfo (a <> b)
instance Monoid (CGInfo a) where
  mempty = CGInfo mempty

addC :: CGEnv a -> RType Core a -> RType Core a -> CG a ()
addC γ t t' = modify $ \(CGInfo scs) -> CGInfo (SubC γ t t':scs)

addBind :: AnnBind a -> CGEnv a -> CGEnv a
addBind (AnnBind x t _) γ = (x, t) : γ

-- Just for Debugging
instance (Show a, Show e, Monoid a) => Show (CG a e) where
 show sa = show $ runFresh $ runStateT sa mempty

-------------------------------------------------------------------------------
-- | generateConstraints is our main entrypoint to this module
-------------------------------------------------------------------------------
generateConstraints :: Core a -> CGInfo a
generateConstraints = runFresh . flip execStateT mempty . synth []

-- run doctests with
--    stack build --copy-compiler-tool doctest
--    stack exec -- doctest -ilib lib/Language/Mist/CGen.hs

-- $
-- >>> synth [] (CUnit ())
-- (RBase (Bind {bindId = "VV###0", bindLabel = ()}) TUnit (CPrim2 Equal (CId "VV###0" ()) (CUnit ()) ()),CGInfo {subCs = []})
-- >>> synth [] (CNumber 1 ())
-- (RBase (Bind {bindId = "VV###0", bindLabel = ()}) TInt (CPrim2 Equal (CId "VV###0" ()) (CNumber 1 ()) ()),CGInfo {subCs = []})
-- >>> let rInt = RBase (Bind "VV" ()) TInt (CBoolean True ())
-- >>> synth [] (CLam (AnnBind "x" rInt ()) (CId "x" ()) ())
-- (RFun (Bind {bindId = "x", bindLabel = ()}) (RBase (Bind {bindId = "VV", bindLabel = ()}) TInt (CBoolean True ())) (RBase (Bind {bindId = "VV", bindLabel = ()}) TInt (CBoolean True ())),CGInfo {subCs = []})
-- >>> synth [] (CPrim2 Plus (CNumber 1 ()) (CNumber 2 ()) ())
-- (RBase (Bind {bindId = "VV###0", bindLabel = ()}) TInt (CPrim2 Equal (CId "VV###0" ()) (CPrim2 Plus (CNumber 1 ()) (CNumber 2 ()) ()) ()),CGInfo {subCs = []})
-- >>> synth [] (CLet (AnnBind "y" rInt ()) (CUnit ()) (CApp (CLam (AnnBind "x" rInt ()) (CId "x" ()) ()) (CId "y" ()) ()) ())
-- (RBase (Bind {bindId = "VV", bindLabel = ()}) TInt (CBoolean True ()),CGInfo {subCs = [SubC [("y",RBase (Bind {bindId = "VV", bindLabel = ()}) TInt (CBoolean True ()))] (RBase (Bind {bindId = "VV###0", bindLabel = ()}) TUnit (CPrim2 Equal (CId "VV###0" ()) (CUnit ()) ())) (RBase (Bind {bindId = "VV", bindLabel = ()}) TInt (CBoolean True ()))]})
-- >>> generateConstraints (CLet (AnnBind "y" rInt ()) (CUnit ()) (CApp (CLam (AnnBind "x" rInt ()) (CId "x" ()) ()) (CId "y" ()) ()) ())
-- CGInfo {subCs = [SubC [("y",RBase (Bind {bindId = "VV", bindLabel = ()}) TInt (CBoolean True ()))] (RBase (Bind {bindId = "VV###0", bindLabel = ()}) TUnit (CPrim2 Equal (CId "VV###0" ()) (CUnit ()) ())) (RBase (Bind {bindId = "VV", bindLabel = ()}) TInt (CBoolean True ()))]}

synth :: CGEnv a -> Core a -> CG a (RType Core a)
synth _ e@CUnit{}    = prim e TUnit
synth _ e@CNumber{}  = prim e TInt
synth _ e@CBoolean{} = prim e TBool
--- is this right? Shouldn't this be a lookup or something?
synth _ e@(CPrim2 o _ _ _) = prim e $ prim2Unpoly o
synth γ (CId x _   ) = single γ x

synth γ (CApp f y _) = do
  RFun x t t' <- synth γ f
  addC γ <$> synth γ y <*> pure t
  pure $ subst1 y (bindId x) t'

synth γ (CTAbs a e _) = do
  RForall a <$> synth γ e

synth γ (CTApp e tau _) = do
  -- if this blows up it's Checker's fault
  RForall (TV a) t <- synth γ e
  -- TODO: tau should be fresh (that is, has its own kvar)
  -- (add at checker time and make CTApp :: Core -> RType -> Core (?) )
  pure $ subst1 tau a t

-- Fake ADT stuff
synth _γ (CTuple _e1 _e2 _) = undefined
synth _γ (CPrim _prim _)    = undefined
synth _γ (CIf _b _e1 _e2 _) = undefined

-- "Bidirectional" "portal" that's made redudant by the fact that we insert
-- all the KVARs at Checker time
synth γ (CLam x e _)
  = bindsRType x <$>
    synth (addBind x γ) e
synth γ (CLet b@(AnnBind _ t1 _) e1 e2 _)
  = do let γ' = addBind b γ
       te1 <- synth γ' e1
       addC γ' te1 t1
       synth γ' e2

prim :: Core a -> Type -> CG a (RType Core a)
prim e t = do
  let l = extractC e
  vv <- refreshId "VV#"
  let reft = CPrim2 Equal (CId vv l) e l
  pure $ RBase (Bind vv l) t reft

single :: CGEnv a -> Id -> CG a (RType Core a)
single γ x = case lookup x γ of
  Just rt@(RBase (Bind v l) _ _)
  -- `x` is already bound, so instead of "re-binding" x we should selfify
  -- (al la Ou et al. IFIP TCS '04)
   | v == x -> do v' <- refreshId "VV#"
                  let rt' = subst1 (CId v' l) x rt
                  pure $ strengthen (CPrim2 Equal (CId v' l) (CId x l) l) rt'
  Just rt -> pure rt
  Nothing -> error $ "Unbound Variable " ++ show x
