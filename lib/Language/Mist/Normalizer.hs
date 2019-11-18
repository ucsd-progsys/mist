{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ScopedTypeVariables #-}
--------------------------------------------------------------------------------
-- | This module contains the code for converting an `Expr` to a "A-Normal" form.
--------------------------------------------------------------------------------

-- TODO make this a typed normalization (preserve t that we get)

module Language.Mist.Normalizer ( liftSigmas, annotateSigmas ) where

import Language.Mist.Types
import Language.Mist.Names
import Language.Mist.Checker (primType)
import Data.Maybe (fromJust)
import Data.Bifunctor (Bifunctor(..))
import Control.Monad.Identity

type ElaboratedExpRType r a = Expr (Maybe (ElaboratedAnnotation r a)) (RType () a, a)
type Env a = [(Id, RType () a)]

-- |
-- prop> (snd <$> annotateSigmas e) == e
annotateSigmas :: ElaboratedExpr r a -> ElaboratedExpRType r a
annotateSigmas =  synth []

extractSigma = fst . extractLoc

instance MonadFresh Identity where
    refreshId = Identity

synth :: forall r a. Env a -> ElaboratedExpr r a -> ElaboratedExpRType r a
synth _ (Unit a) = Unit (liftType a TUnit, a)
synth _ (Number i a) = Number i (liftType a TInt, a)
synth _ (Boolean b a) = Boolean b (liftType a TBool, a)
synth _ (Prim p a) = Prim p (liftType a $ runIdentity $ primType p, a)
synth env e@(Id x _) = (fromJust $ lookup x env,) <$> e

synth env (If e1 e2 e3 l) = If e1' e2' e3' (extractSigma e2', l)
  where
    e1' = synth env e1
    e2' = synth env e2
    e3' = synth env e3

synth env (Unpack (Bind x lx) (Bind y ly) e1 e2 loc) =
  Unpack (Bind x (tx, lx)) (Bind y (ty, ly)) e1' e2' (extractSigma e2', loc)
  where
    e1' = synth env e1
    e2' = synth ((x, tx):(y, ty):env) e2
    RIExists _ tx ty = extractSigma e1'

synth env (ILam b@(AnnBind x (Just tx) loc) e l) =
  ILam (AnnBind x (Just tx) (tx', loc)) e' (t', l)
  where
  e' = synth env e
  tx' = liftType loc tx
  t' = RIFun (first (const ()) b) tx' (extractSigma e')

synth _env (ILam (AnnBind _ Nothing _) _ _) =
    error "should not occur after Elaboration"

synth env (Let b e1 e2 loc) = Let b' e1' e2' (extractSigma e2', loc)
  where
  (b', e1', e2') = go b

  go b@(AnnBind x (Just (ElabAssume tx)) _) = ((dropPreds tx,) <$> b, e1',e2')
    where
      e1' = (dropPreds tx,) <$> e1
      e2' = synth ((x, dropPreds tx): env) e2

  go b@(AnnBind x (Just (ElabRefined tx)) _) = ((dropPreds tx,) <$> b, e1',e2')
    where
      e1' = check ((x, dropPreds tx):env) e1 $ dropPreds tx
      e2' = synth ((x, dropPreds tx):env) e2

  -- Unrefined
  -- Not allowed to be recursive
  go b@(AnnBind x (Just (ElabUnrefined _typ)) _) = ((tx,) <$> b, e1',e2')
    where
      e1' = synth env e1
      tx = extractSigma e1'
      e2' = synth ((x, tx):env) e2

  go (AnnBind _ Nothing _) = error "INTERNAL ERROR: annotation missing on let"

synth _ (Lam (AnnBind _ Nothing _) _ _) = error "should not occur"
synth _ (Lam (AnnBind _ (Just (ElabAssume _)) _) _ _) = error "should not occur"

synth env (Lam b@(AnnBind x (Just (ElabRefined tx)) loc) e l) =
    Lam ((dropPreds tx,)<$>b) e' (RFun (Bind x loc) (dropPreds tx) (dropPreds $ extractSigma e'), l)
  where e' = synth ((x, dropPreds tx):env) e

synth env (Lam b@(AnnBind x (Just (ElabUnrefined typ)) loc) e l) =
    Lam ((liftType loc typ,)<$>b) e' (RFun (Bind x loc) (liftType loc typ) (extractSigma e'), l)
  where e' = synth ((x, liftType loc typ):env) e
  -- NB: this ist liftType because in synthesis mode we have no more info, but in checking mode, we should propogate type information

synth env (TApp e typ loc) = TApp e' typ (t', loc)
  where
    e' = synth env e
    t' = case extractSigma e' of
              RForall tvar t' -> substReftReft (unTV tvar |-> liftType loc typ) t'
              RForallP tvar t' -> substReftReft (unTV tvar |-> liftType loc typ) t'
              _ -> error "should not happen"

synth env (TAbs tvar e l) =
  TAbs tvar e' (RForall tvar (extractSigma e'),l)
    where e' = synth env e

synth env (App e1 e2 l) = App e1' e2' (descend $ extractSigma e2', l)
  where
    e1' = synth env e1
    e2' = synth env e2

check :: Env a -> ElaboratedExpr r a -> RType () a -> Expr (Maybe (ElaboratedAnnotation r a)) (RType () a, a)
check env (If e1 e2 e3 l) t = If e1' e2' e3' (t, l)
  where
    e1' = synth env e1
    e2' = check env e2 t
    e3' = check env e3 t

check env (Unpack (Bind x lx) (Bind y ly) e1 e2 loc) t =
  Unpack (Bind x (tx, lx)) (Bind y (ty, ly)) e1' e2' (extractSigma e2', loc)
  where
    e1' = synth env e1
    e2' = check ((x, tx):(y, ty):env) e2 t
    RIExists _ tx ty = extractSigma e1'

check env (ILam (Bind x loc) e l) t'@(RIFun _ ty t) =
  ILam (Bind x (ty,loc)) e' (t', l)
  where
  e' = check env e t

check env (Let b e1 e2 loc) t = Let b' e1' e2' (t, loc)
  where
  (b', e1', e2') = go b

  go b@(AnnBind x (Just (ElabAssume tx)) _) = ((dropPreds tx,) <$> b, e1',e2')
    where
      e1' = (dropPreds tx,) <$> e1
      e2' = check ((x, dropPreds tx): env) e2 t

  go b@(AnnBind x (Just (ElabRefined tx)) _) = ((dropPreds tx,) <$> b, e1',e2')
    where
      e1' = check ((x, dropPreds tx):env) e1 $ dropPreds tx
      e2' = check ((x, dropPreds tx):env) e2 t

  -- Unrefined
  -- Not allowed to be recursive
  go b@(AnnBind x (Just (ElabUnrefined _)) _) = ((tx,) <$> b, e1',e2')
    where
      e1' = synth env e1
      tx = extractSigma e1'
      e2' = check ((x, tx):env) e2 t

  go (AnnBind _ Nothing _) = error "INTERNAL ERROR: annotation missing on let"


check env (Lam (Bind x loc) e l) t'@(RFun y ty t) =
  let ty' = substReftPred (bindId y |-> x) ty
      e' = check ((x, ty):env) e (substReftPred (bindId y |-> x) t) in
    Lam (Bind x (ty',loc)) e' (t',l)

-- I don't think the names matter here. If they do ... oops
check env (TAbs tvar' e loc) t'@(RForall (TV tvar) t) =
  let e' = check env e (substReftType (tvar |-> TVar tvar') t) in
    TAbs tvar' e' (t',loc)
check env (TAbs tvar' e loc) t'@(RForallP (TV tvar) t) =
  let e' = check env e (substReftType (tvar |-> TVar tvar') t) in
    TAbs tvar' e' (t',loc)

check env (App e1 e2 loc) t = App e1' e2' (t,loc)
  where
    e2' = synth env e2
    e1' = check env e1 (RFun (Bind "" loc) (extractSigma e2') t)

check env e _ = synth env e

--------------------------------------------------------------------------------
-- | Insert explicit unpacking of implicit sigmas
--------------------------------------------------------------------------------
type SigmaBinds r a = [(Id, Id, ElaboratedExpr r a)]

liftSigmas :: ElaboratedExpr r a -> ElaboratedExpr r a
liftSigmas e = runFresh (anfSigmas $ annotateSigmas e)

anfSigmas :: (MonadFresh m) => ElaboratedExpRType r a -> m (ElaboratedExpr r a)
anfSigmas e@Number{} = pure $ snd <$> e
anfSigmas e@Boolean{} = pure $ snd <$> e
anfSigmas e@Unit{} = pure $ snd <$> e
anfSigmas e@Id{} =  uncurry stitchUnpacks <$> immSigmas e
anfSigmas e@Prim{} = uncurry stitchUnpacks <$> immSigmas e
anfSigmas (If e1 e2 e3 l) = do
  (bs, e1') <- immSigmas e1
  e2' <- anfSigmas e2
  e3' <- anfSigmas e3
  pure $ stitchUnpacks bs $ If e1' e2' e3' $ snd l

anfSigmas (Let (AnnBind _x Nothing _) _e1 _e2 _l) =
  error "this shouldn't happen"
anfSigmas (Let b@(AnnBind _ (Just (ElabAssume _)) _) e1 e2 l) = do
  e2' <- anfSigmas e2
  pure $ Let (snd <$> b) (snd <$> e1) e2' $ snd l
anfSigmas (Let b e1 e2 l) = do
  (bs, e1') <- immSigmas e1
  e2' <- anfSigmas e2
  pure $ stitchUnpacks bs $ Let (snd <$> b) e1' e2' $ snd l
anfSigmas (App e1 e2 l) = do
  (bs1, e1') <- immSigmas e1
  (bs2, e2')  <- immSigmas e2
  pure $ stitchUnpacks (bs1 <> bs2) (App e1' e2' (snd $ l))

anfSigmas (Lam (AnnBind _ Nothing _) _ _) =
  error "this shouldn't happen"
anfSigmas (Lam (AnnBind _x (Just ElabAssume{}) _) _e _l) =
  error "this shouldn't happen"
anfSigmas (Lam b e l) =
  Lam (snd <$> b) `flip` (snd $ l) <$> anfSigmas e

anfSigmas (ILam b e l) = do
  (e') <- anfSigmas e
  pure (ILam (snd <$> b) e' (snd $ l))
anfSigmas (TApp e typ l) = do
  (e') <- anfSigmas e
  pure (TApp e' typ (snd $ l))

anfSigmas (TAbs tv e l) = do
  (e') <- anfSigmas e
  pure (TAbs tv e' (snd $ l))
anfSigmas (Unpack _x _y _e1 _e2 _l) = error "todo?"

immSigmas :: (MonadFresh m) => ElaboratedExpRType r a -> m (SigmaBinds r a, ElaboratedExpr r a)
immSigmas e | (RIExists b _ t', l) <- extractLoc e = do
  let tag = extractAnn e
  (x, y) <- freshSigmaNames (bindId b)
  (bs, e') <- immSigmas (AnnId y tag (t', l))
  pure ((x, y, snd <$> e):bs, e')
immSigmas e = pure ([], snd <$> e)

stitchUnpacks :: SigmaBinds r a -> ElaboratedExpr r a -> ElaboratedExpr r a
stitchUnpacks [] e' = e'
stitchUnpacks ((x, y, e):bs) e' =
  AnnUnpack (AnnBind x () l) (AnnBind y () l) e (stitchUnpacks bs e') (extractAnn e') (extractLoc e')
  where
    l = extractLoc e

descend :: RType r a -> RType r a
descend (RIFun _ _ t') = descend t'
descend (RFun _ _ t') = t'
descend _ = error "shouldn't happen"

dropPreds :: Bifunctor b => b a c -> b () c
dropPreds = first (const ())

freshSigmaNames :: (MonadFresh m) => Id -> m (Id, Id)
freshSigmaNames x = do
  x' <- refreshId x
  y <- refreshId $ "unpackedY" ++ cSEPARATOR
  pure (x', y)

liftType :: a -> Type -> RType () a
liftType loc (TVar alpha) = RBase (Bind "x" loc) (TVar alpha) ()
liftType loc TUnit = RBase (Bind "x" loc) TUnit ()
liftType loc TInt = RBase (Bind "x" loc) TInt ()
liftType loc TBool = RBase (Bind "x" loc) TBool ()
liftType loc (t1 :=> t2) = RFun (Bind "x" loc) (liftType loc t1) (liftType loc t2)
liftType loc (TCtor ctor types) = RApp ctor (fmap (second (liftType loc)) types)
liftType loc (TForall tvar typ) = RForall tvar (liftType loc typ)
