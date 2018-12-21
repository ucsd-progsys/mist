-- Extensions only needed for (Show (CG a e)) (for debugging)
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

module Language.Mist.CGen ( generateConstraints ) where

-- TODO: Do we need to run a Uniqify pass before we run this module?
-- Matt: We should uniquify at the beginning and then maintain the unique names property

import           Language.Mist.Types
import           Language.Mist.Names
import           Language.Mist.Checker (prim2Unpoly)
import           Control.Monad.State.Strict
-- import qualified Language.Fixpoint.Types as F

data SubC a = SubC [(Id, RType Core a)] (RType Core a) (RType Core a)
  deriving Show
data CGInfo a = CGInfo { subCs :: [SubC a] }
  deriving Show

type CG a = StateT (CGInfo a) Fresh
type CGEnv a = [(Id, RType Core a)]

instance MonadFresh (CG a) where
  refreshId = lift . refreshId
  popId     = lift popId
  lookupId  = lift . lookupId

-- Just for Debugging
instance (Show a, Show e, Monoid a) => Show (CG a e) where
 show sa = show $ runFresh $ runStateT sa mempty

instance Semigroup (CGInfo a) where
  CGInfo a <> CGInfo b = CGInfo (a <> b)
instance Monoid (CGInfo a) where
  mempty = CGInfo mempty

addC :: CGEnv a -> RType Core a -> RType Core a -> CG a ()
addC γ t t' = modify $ \(CGInfo scs) -> CGInfo (SubC γ t t':scs)

addBind :: AnnBind a -> CGEnv a -> CGEnv a
addBind (AnnBind x t _) γ = (x, t) : γ

generateConstraints :: Core a -> CGInfo a
generateConstraints = runFresh . flip execStateT mempty . synth []

synth :: CGEnv a -> Core a -> CG a (RType Core a)
synth _ e@CUnit{}    = prim e TUnit
synth _ e@CNumber{}  = prim e TInt
synth _ e@CBoolean{} = prim e TBool
--- is this right? Shouldn't this be a lookup or something?
synth _ e@(CPrim2 o _ _ _) = prim e $ prim2Unpoly o
synth γ (CId x _   ) = single γ x

synth γ (CApp f y _) = do
  RFun x t t' <- synth γ f
  -- TODO: Enforce this in the refinement type
  let CId y' _ = y
  addC γ <$> single γ y' <*> pure t
  pure $ subst1 y (bindId x) t'

synth γ (CTAbs a e _) = do
  RForall a <$> synth γ e

synth γ (CTApp e tau _) = do
  RForall (TV a) t <- synth γ e
  pure $ subst1 tau a t

  -- Fake ADT stuff
synth _γ (CTuple _e1 _e2 _) = undefined
synth _γ (CPrim _prim _) = undefined
synth _γ (CIf _b _e1 _e2 _) = undefined

-- "Bidirectional" "portal" that's made redudant by the fact that we insert
-- all the KVARs at parse time
synth γ (CLam x e _)
  = bindsRType x <$>
    synth (addBind x γ) e
synth γ  (CLet b@(AnnBind _ t1 _) e1 e2 _)
  = synth γ e1 >>=
    flip (addC γ) t1 >>
    synth (addBind b γ) e2

prim :: Core a -> Type -> CG a (RType Core a)
prim e t = do
  let l = extractC e
  vv <- refreshId "VV"
  let expr = CPrim2 Equal (CId vv l) e l
  pure $ RBase (Bind vv l) t expr

single :: CGEnv a -> Id -> CG a (RType Core a)
single γ x = case lookup x γ of
  Just rt@(RBase (Bind v l) _ _)
   | v == x -> do v' <- refreshId "VV"
                  let rt' = subst1 (CId v' l) x rt
                  pure $ strengthen (CPrim2 Equal (CId v' l) (CId x l) l) rt'
  Just rt -> pure rt
  Nothing -> error $ "Unbound Variable " ++ show x
