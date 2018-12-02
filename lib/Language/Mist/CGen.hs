{-# LANGUAGE DeriveAnyClass #-}
module Language.Mist.CGen ( generateConstraints ) where

import Language.Mist.Types
import Control.Monad.State.Strict

data SubC a = SubC [(Id, RPoly a)] (RPoly a) (RPoly a)

data CGInfo a = CGInfo { subCs :: [SubC a] }
type CG a = State (CGInfo a)

instance Semigroup (CGInfo a) where
  CGInfo a <> CGInfo b = CGInfo (a <> b)
instance Monoid (CGInfo a) where
  mempty = CGInfo mempty

subC γ t t' = CGInfo { subCs = [ SubC γ t t' ] }

generateConstraints = generateConstraints' []

generateConstraints' :: [(Id, RPoly a)] -> Core a -> CG a ()
generateConstraints' γ (CLet (CBind b s _) e1 e2 _)
  = check γ s e1 >> generateConstraints' ((b,s):γ) e2
generateConstraints' _ (CPrim "()" _)
  = pure mempty
generateConstraints' _ _
 = error "generateConstraints"

check :: [(Id, RPoly a)] -> RPoly a -> Core a -> CG a ()
check γ t (CLet (CBind b s _) e1 e2 _)
  = do check γ s e1
       te <- synth ((b,s):γ) e2
       modify (<> subC ((b,s):γ) te t)

check γ t (CTAbs a e _) = undefined
check γ t (CLam  x e _) = undefined

check γ t e
  = do te <- synth γ e
       modify (<> subC γ te t)

synth :: [(Id, RPoly a)] -> Core a -> CG a (RPoly a)
synth γ (CNumber i l) = undefined
  -- need to pass around a fresh variable supply...
  -- = (mempty, RForall [] $ RBase (Bind "" l) TInt (Prim2 Equal
synth γ (CBoolean b _) = undefined
synth γ (CId x _) = undefined
synth γ (CPrim x _) = undefined
synth γ (CIf b e1 e2 _) = undefined
synth γ (CLet x e1 e2 _) = undefined
synth γ (CTuple e1 e2 _) = undefined
synth γ (CApp f x _) = undefined
  -- better make sure we're in ANF...
synth γ (CLam x e _) = undefined
synth γ (CTApp e t _) = undefined
synth γ (CTAbs as e _) = undefined
