-- Extensions only needed for (Show (CG a e)) (for debugging)
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

module Language.Mist.CGen ( generateConstraints ) where
-- TODO: Do we need to run a Uniqify pass before we run this module?
import           Language.Mist.Types
import           Control.Monad.State.Strict
-- import qualified Language.Fixpoint.Types as F

data SubC a = SubC [(Id, RPoly Core a)] (RPoly Core a) (RPoly Core a)
  deriving Show
data CGInfo a = CGInfo { subCs :: [SubC a], fresh :: Int }
  deriving Show

type CG a = State (CGInfo a)
type CGEnv a = [(Id, RPoly Core a)]

-- Just for Debugging
instance (Show a, Show e, Monoid a) => Show (CG a e) where
 show sa = show $ runState sa mempty

instance Semigroup (CGInfo a) where
  CGInfo a n <> CGInfo b m = CGInfo (a <> b) (n + m)
instance Monoid (CGInfo a) where
  mempty = CGInfo mempty 0

addC :: CGEnv a -> RPoly Core a -> RPoly Core a -> CG a ()
addC γ t t' = modify $ \(CGInfo scs n) -> CGInfo ((SubC γ t t'):scs) n

addBinds = flip (foldr addB)
addB (AnnBind x t _) γ = (x, t) : γ

generateConstraints :: Core a -> CGInfo a
generateConstraints = flip execState mempty . synth []

synth :: CGEnv a -> Core a -> CG a (RPoly Core a)
synth _ e@CUnit{}    = pure $ prim e (TCtor (CT "()") [])
synth _ e@CNumber{}  = pure $ prim e TInt
synth _ e@CBoolean{} = pure $ prim e TBool
--- is this right? Shouldn't this be a lookup or something?
synth _ e@CPrim2{}   = pure $ prim e undefined
synth γ (CId x _   ) = pure $ single γ x

synth γ (CApp f y _) = do
  RForall [] (RFun x t t') <- synth γ f
  -- TODO: Enforce this in the refinement type
  let CId y' _ = y
  addC γ (single γ y') (RForall [] t)
  pure $ subst y x t'

synth γ (CTAbs as e _) = do
  RForall as' t <- synth γ e
  pure $ RForall (as' ++ as) t

synth γ (CTApp e tau _) = do
  RForall (a : as) t <- synth γ e
  pure $ RForall as $ subst tau a t

  -- Fake ADT stuff
synth _γ (CTuple _e1 _e2 _) = undefined
synth _γ (CGetItem _e1 _e2 _) = undefined
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

-- (needs to be refreshed)
prim :: Core a -> Type -> RPoly Core a
prim e t = RForall [] $ RBase vv t expr
  where l = extractC e
        vv = Bind "VV" l
        expr = CPrim2 Equal (CId "VV" l) e l
  -- need to pass around a fresh variable supply...
  -- RForall [] $ RBase (Bind "" l) TInt (Prim2 Equal
single :: CGEnv a -> Id -> RPoly Core a
single _γ _e = undefined -- HEREHEREHERE
subst = undefined
