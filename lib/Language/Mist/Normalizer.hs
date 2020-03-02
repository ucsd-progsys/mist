{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE BangPatterns #-}
--------------------------------------------------------------------------------
-- | This module contains the code for converting an `Expr` to a "A-Normal" form.
--------------------------------------------------------------------------------

-- TODO make this a typed normalization (preserve t that we get)

module Language.Mist.Normalizer ( liftSigmas, annotateSigmas ) where

import Language.Mist.Types
import Language.Mist.Names
import Language.Mist.Checker (primType)
import Data.Maybe (fromMaybe)
import Data.Bifunctor (Bifunctor(..))
import Control.Monad.Identity

type ElaboratedExpRType r a = Expr (Maybe (ElaboratedAnnotation r a)) (RType () a, a)
type Env a = [(Id, RType () a)]

-- |
-- prop> (snd <$> annotateSigmas e) == e
annotateSigmas :: ElaboratedExpr r a -> ElaboratedExpRType r a
annotateSigmas e = synth [] e

extractSigma = fst . extractLoc

instance MonadFresh Identity where
    refreshId = Identity

synth :: forall r a. Env a -> ElaboratedExpr r a -> ElaboratedExpRType r a
synth _ (AnnUnit tag a) = AnnUnit tag (liftType a TUnit, a)
synth _ (AnnNumber i tag a) = AnnNumber i tag (liftType a TInt, a)
synth _ (AnnBoolean b tag a) = AnnBoolean b tag (liftType a TBool, a)
synth _ (AnnPrim p tag a) = AnnPrim p tag (liftType a $ runIdentity $ primType p, a)
synth env e@(AnnId x _ _) = (fromMaybe (error $ "lookup failure: " <> x) $ lookup x env,) <$> e

synth env (AnnIf e1 e2 e3 tag l) = AnnIf e1' e2' e3' tag (extractSigma e2', l)
  where
    e1' = synth env e1
    e2' = synth env e2
    e3' = synth env e3

synth env (AnnUnpack (Bind x lx) (Bind y ly) e1 e2 tag loc) =
  AnnUnpack (Bind x (tx, lx)) (Bind y (ty, ly)) e1' e2' tag (extractSigma e2', loc)
  where
    e1' = synth env e1
    e2' = synth ((x, tx):(y, ty):env) e2
    RIExists _ tx ty = extractSigma e1'

synth env (AnnILam b@(AnnBind x (Just tx) loc) e tag l) =
  AnnILam (AnnBind x (Just tx) (tx', loc)) e' tag (t', l)
  where
  e' = synth env e
  tx' = liftType loc tx
  t' = RIFun (first (const ()) b) tx' (extractSigma e')

synth env (AnnILam b@(AnnBind _ Nothing loc) e tag l) =
  AnnILam ((tx',) <$> b) e' tag (t', l)
  where
  e' = synth env e
  tx' = liftType loc TUnit
  t' = RIFun (first (const ()) b) tx' (extractSigma e')

synth env (AnnLet b e1 e2 tag loc) = AnnLet b' e1' e2' tag (extractSigma e2', loc)
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

  go b@(AnnBind x (Just (ElabUnrefined _typ)) _) = ((tx,) <$> b, e1',e2')
    where
      e1' = synth env e1
      tx = dropLeadingSigmas $ extractSigma e1'
      e2' = synth ((x, tx):env) e2

  go (AnnBind _ Nothing _) = error "INTERNAL ERROR: annotation missing on let"

synth _ (AnnLam (AnnBind _ Nothing _) _ _ _) = error "should not occur"
synth _ (AnnLam (AnnBind _ (Just (ElabAssume _)) _) _ _ _) = error "should not occur"

synth env (AnnLam b@(AnnBind x (Just (ElabRefined tx)) _) e tag l) =
  AnnLam ((dropPreds tx,) <$> b) e' tag (RFun (dropPreds b) (dropPreds tx) (dropPreds $ extractSigma e'), l)
  where
    e' = synth ((x, dropPreds tx):env) e

synth env (AnnLam b@(AnnBind x (Just (ElabUnrefined typ)) loc) e tag l) =
  AnnLam ((liftType loc typ,) <$> b) e' tag (RFun (dropPreds b) (liftType loc typ) (extractSigma e'), l)
  where e' = synth ((x, liftType loc typ):env) e
  -- NB: this ist liftType because in synthesis mode we have no more info, but in checking mode, we should propogate type information

synth env (AnnTApp e typ tag loc) = AnnTApp e' typ tag (t', loc)
  where
    e' = synth env e
    t' = case extractSigma e' of
              RForall tvar t' -> substReftReft (unTV tvar |-> liftType loc typ) t'
              RForallP tvar t' -> substReftReft (unTV tvar |-> liftType loc typ) t'
              _ -> error "should not happen"

synth env (AnnTAbs tvar e tag l) =
  AnnTAbs tvar e' tag (RForall tvar (extractSigma e'), l)
  where e' = synth env e

synth env (AnnApp e1 e2 tag l) = AnnApp e1' e2' tag (descend $ extractSigma e1', l)
  where
    e1' = synth env e1
    e2' = synth env e2

check :: Env a -> ElaboratedExpr r a -> RType () a -> Expr (Maybe (ElaboratedAnnotation r a)) (RType () a, a)
check env (AnnIf e1 e2 e3 tag l) t = AnnIf e1' e2' e3' tag (t, l)
  where
    e1' = synth env e1
    e2' = check env e2 t
    e3' = check env e3 t

check env (AnnUnpack (Bind x lx) (Bind y ly) e1 e2 tag loc) t =
  AnnUnpack (Bind x (tx, lx)) (Bind y (ty, ly)) e1' e2' tag (extractSigma e2', loc)
  where
    e1' = synth env e1
    e2' = check ((x, tx):(y, ty):env) e2 t
    RIExists _ tx ty = extractSigma e1'

check env (AnnILam (AnnBind x btag loc) e tag l) t'@(RIFun _ tx t) =
  AnnILam (AnnBind x btag (tx, loc)) e' tag (t', l)
  where
  e' = check env e t

check env (AnnLet b e1 e2 tag loc) t = AnnLet b' e1' e2' tag (t, loc)
  where
  (b', e1', e2') = go b

  go b@(AnnBind x (Just (ElabAssume tx)) _) = ((dropPreds tx,) <$> b, e1', e2')
    where
      e1' = (dropPreds tx,) <$> e1
      e2' = check ((x, dropPreds tx): env) e2 t

  go b@(AnnBind x (Just (ElabRefined tx)) _) = ((dropPreds tx,) <$> b, e1', e2')
    where
      e1' = check ((x, dropPreds tx):env) e1 $ dropPreds tx
      e2' = check ((x, dropPreds tx):env) e2 t

  -- Unrefined
  -- Not allowed to be recursive
  go b@(AnnBind x (Just (ElabUnrefined _)) _) = ((tx,) <$> b, e1',e2')
    where
      e1' = synth env e1
      tx = dropLeadingSigmas $ extractSigma e1'
      e2' = check ((x, tx):env) e2 t

  go (AnnBind _ Nothing _) = error "INTERNAL ERROR: annotation missing on let"


check env (AnnLam (AnnBind x btag loc) e tag l) t'@(RFun y ty t) =
  let ty' = substReftPred (bindId y |-> x) ty
      e' = check ((x, ty):env) e (substReftPred (bindId y |-> x) t)
  in AnnLam (AnnBind x btag (ty', loc)) e' tag (t', l)

-- I don't think the names matter here. If they do ... oops
check env (AnnTAbs tvar' e tag loc) t'@(RForall (TV tvar) t) =
  let e' = check env e (substReftType (tvar |-> TVar tvar') t)
  in AnnTAbs tvar' e' tag (t', loc)
check env (AnnTAbs tvar' e tag loc) t'@(RForallP (TV tvar) t) =
  let e' = check env e (substReftType (tvar |-> TVar tvar') t)
  in AnnTAbs tvar' e' tag (t', loc)

check env (AnnApp e1 e2 tag loc) t = AnnApp e1' e2' tag (t, loc)
  where
    e2' = synth env e2
    e1' = check env e1 (RFun (Bind "" loc) (extractSigma e2') t)

check env e _ = synth env e

dropLeadingSigmas :: RType r a -> RType r a
dropLeadingSigmas (RIExists _ _ t') = dropLeadingSigmas t'
dropLeadingSigmas t = t

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
anfSigmas (Let b@(AnnBind _ (Just ElabAssume{}) _) e1 e2 l) = do
  e2' <- anfSigmas e2
  pure $ Let (snd <$> b) (snd <$> e1) e2' $ snd l
anfSigmas (Let b e1 e2 l) = do
  (bs, e1') <- immSigmas e1
  e2' <- anfSigmas e2
  pure $ stitchUnpacks bs $ Let (snd <$> b) e1' e2' $ snd l

anfSigmas e@App{} = do
  (bs, e') <- anfAppSigmas e
  pure $ stitchUnpacks bs e'

anfSigmas (Lam (AnnBind _ Nothing _) _ _) =
  error "this shouldn't happen"
anfSigmas (Lam (AnnBind _x (Just ElabAssume{}) _) _e _l) =
  error "this shouldn't happen"
anfSigmas (Lam b e l) =
  Lam (snd <$> b) `flip` (snd l) <$> anfSigmas e

anfSigmas (ILam b e l) = do
  e' <- anfSigmas e
  pure (ILam (snd <$> b) e' (snd l))
anfSigmas (TApp e typ l) = do
  e' <- anfSigmas e
  pure (TApp e' typ (snd l))

anfSigmas (TAbs tv e l) = do
  e' <- anfSigmas e
  pure (TAbs tv e' (snd l))
-- anfSigmas (Unpack x y e1 e2 l) = error "todo?"
anfSigmas e@Unpack{} = pure (snd <$> e)

anfAppSigmas :: (MonadFresh m) => ElaboratedExpRType r a -> m (SigmaBinds r a, ElaboratedExpr r a)
anfAppSigmas (AnnApp e1 e2 tag l) = do
  (bs1, e1') <- anfAppSigmas e1
  (bs2, e2') <- immSigmas e2
  pure (bs1 <> bs2, AnnApp e1' e2' tag (snd l))
anfAppSigmas e = do
  immSigmas e

immSigmas :: (MonadFresh m) => ElaboratedExpRType r a -> m (SigmaBinds r a, ElaboratedExpr r a)
immSigmas e | (RIExists b _ t', l) <- extractLoc e = do
  let tag = extractAnn e
  (x, y) <- freshSigmaNames (bindId b)
  (bs, e') <- immSigmas (AnnId y tag (t', l))
  pure ((x, y, snd <$> e):bs, e')
immSigmas e@Id{} = pure ([], snd <$> e)
immSigmas e@Prim{} = pure ([], snd <$> e)
immSigmas e = do
  e' <- anfSigmas e
  pure ([], e')

stitchUnpacks :: SigmaBinds r a -> ElaboratedExpr r a -> ElaboratedExpr r a
stitchUnpacks [] e' = e'
stitchUnpacks ((x, y, e):bs) e' =
  AnnUnpack (AnnBind x () l) (AnnBind y () l) e (stitchUnpacks bs e') (extractAnn e') (extractLoc e')
  where
    l = extractLoc e

descend :: (PPrint r) => RType r a -> RType r a
descend (RIFun _ _ t') = descend t'
descend (RFun _ _ t') = t'
descend (RRTy _ rt _) = descend rt
descend (RIExists _ _ rt) = descend rt
descend t = error $ "descend on non-function: " <> pprint t

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
