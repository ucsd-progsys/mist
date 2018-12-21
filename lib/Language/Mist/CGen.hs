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

data SubC a = SubC [(Id, RPoly Core a)] (RPoly Core a) (RPoly Core a)
  deriving Show
data CGInfo a = CGInfo { subCs :: [SubC a], fresh :: Int }
  deriving Show

type CG a = StateT (CGInfo a) Fresh
type CGEnv a = [(Id, RPoly Core a)]

instance MonadFresh (CG a) where
  refreshId = lift . refreshId
  popId     = lift popId
  lookupId  = lift . lookupId

-- Just for Debugging
instance (Show a, Show e, Monoid a) => Show (CG a e) where
 show sa = show $ runFresh $ runStateT sa mempty

instance Semigroup (CGInfo a) where
  CGInfo a n <> CGInfo b m = CGInfo (a <> b) (n + m)
instance Monoid (CGInfo a) where
  mempty = CGInfo mempty 0

addC :: CGEnv a -> RPoly Core a -> RPoly Core a -> CG a ()
addC γ t t' = modify $ \(CGInfo scs n) -> CGInfo ((SubC γ t t'):scs) n

addBinds = flip (foldr addB)
addB (AnnBind x t _) γ = (x, t) : γ

generateConstraints :: Core a -> CGInfo a
generateConstraints = runFresh . flip execStateT mempty . synth []

synth :: CGEnv a -> Core a -> CG a (RPoly Core a)
synth _ e@CUnit{}    = prim e TUnit
synth _ e@CNumber{}  = prim e TInt
synth _ e@CBoolean{} = prim e TBool
--- is this right? Shouldn't this be a lookup or something?
synth _ e@(CPrim2 o _ _ _) = prim e $ prim2Unpoly o
synth γ (CId x _   ) = single γ x

synth γ (CApp f y _) = do
  RForall [] (RFun x t t') <- synth γ f
  -- TODO: Enforce this in the refinement type
  let CId y' _ = y
  addC γ <$> single γ y' <*> pure (RForall [] t)
  pure $ RForall [] $ subst1 y (bindId x) t'

synth γ (CTAbs as e _) = do
  RForall as' t <- synth γ e
  pure $ RForall (as' ++ as) t

synth γ (CTApp e tau _) = do
  RForall (TV a : as) t <- synth γ e
  pure $ RForall as $ subst1 tau a t

  -- Fake ADT stuff
synth _γ (CTuple _e1 _e2 _) = undefined
synth _γ (CPrim _prim _) = undefined
synth _γ (CIf _b _e1 _e2 _) = undefined

-- "Bidirectional" "portal" that's made redudant by the fact that we insert
-- all the KVARs at parse time
synth γ (CLam xs e _)
  = bindsRType xs <$>
    synth (addBinds xs γ) e
synth γ  (CLet b@(AnnBind _ t1 _) e1 e2 _)
  = synth γ e1 >>=
    flip (addC γ) t1 >>
    synth (addB b γ) e2

prim :: Core a -> Type -> CG a (RPoly Core a)
prim e t = refresh $ RForall [] $ RBase vv t expr
  where l = extractC e
        vv = Bind "VV" l
        expr = CPrim2 Equal (CId "VV" l) e l

single :: CGEnv a -> Id -> CG a (RPoly Core a)
single γ x = case lookup x γ of
  -- TODO: why do we need to refresh this? Just blindly following the paper
  -- here
  Just rt@(RForall _ (RBase (Bind v l) _ _))
   | v == x -> do rt'@(RForall [] (RBase (Bind v' _) _ _)) <- refresh rt
                  pure $ strengthen (CPrim2 Equal (CId v' l) (CId x l) l) rt'
  Just rt -> pure rt
  Nothing -> error $ "Unbound Variable " ++ show x
