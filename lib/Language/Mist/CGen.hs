{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeApplications #-}

--------------------------------------------------------------------------------
-- | This module generates refinement type constraints
-- | (see Cosman and Jhala, ICFP '17)
--------------------------------------------------------------------------------


module Language.Mist.CGen
  ( generateConstraints
  , Constraint (..)
  ) where

-- TODO: Do we need to run a Uniqify pass before we run this module?
-- Matt: We should uniquify at the beginning and then maintain the unique names property

-- TODO: flatten RRTy

import Language.Mist.Types
import Language.Mist.Names

-------------------------------------------------------------------------------
-- Data Structures
-------------------------------------------------------------------------------
type Env r a = [(Id, RType r a)]

-------------------------------------------------------------------------------
-- | generateConstraints is our main entrypoint to this module
-------------------------------------------------------------------------------
generateConstraints :: (Predicate r) => ElaboratedExpr r a -> Constraint r
generateConstraints = fst . runFresh . cgen []

cgen :: (Predicate r) =>
        Env r a -> ElaboratedExpr r a -> Fresh (Constraint r, RType r a)
cgen _ e@Unit{} = (Head true,) <$> prim e
cgen _ e@Number{} = (Head true,) <$> prim e
cgen _ e@Boolean{} = (Head true,) <$> prim e
cgen _ e@Prim2{} = (Head true,) <$> prim e -- TODO: should this be a lookup?
                                      -- how should prims be handled?
cgen env (Id x _) = (Head true,) <$> single env x
cgen _env (If _e1 _e2 _e3 _) = error "TODO"

-- TODO: recursive let?
cgen env (Let bind@AnnBind{_aBindType = Right _} e1 e2 _) = do
  let x = bindId bind
  (c1, t1) <- cgen env e1
  (c2, t2) <- cgen ((x, t1):env) e2
  tHat <- fresh (eraseRType t2) (extract e2)
  let c = CAnd [c1, (generalizedImplication x t1 c2)]
  pure (CAnd [c, (t2 `sub` tHat)], tHat)
cgen env (Let bind@AnnBind{_aBindType = Left tx} e1 e2 _) = do
  let x = bindId bind
  (c1, t1) <- cgen env e1
  (c2, t2) <- cgen ((x, tx):env) e2
  tHat <- fresh (eraseRType t2) (extract e2)
  let c = CAnd [c1, (generalizedImplication x tx c2)]
  pure (CAnd [c, (t1 `sub` tx), (t2 `sub` tHat)], tHat)

cgen env (App e (Id y _) _) = do
  (c, RFun x t t') <- cgen env e
  ty <- single env y
  let cy = ty `sub` t
  pure (CAnd [c, cy], substReftPred1 y (bindId x) t')
cgen _ (App _ _ _) = error "argument is non-variable"
cgen env (Lam bind@AnnBind{_aBindType = Right typ} e _) = do
  let x = bindId bind
  tHat <- fresh typ (bindLabel bind)
  (c, t) <- cgen ((x, tHat):env) e
  pure (generalizedImplication x tHat c, RFun Bind{_bindId = x, _bindLabel = bindLabel bind} tHat t)
cgen env (Lam bind@AnnBind{_aBindType = Left tx} e _) = do
  let x = bindId bind
  (c, t) <- cgen ((x, tx):env) e
  pure (generalizedImplication x tx c, RFun Bind{_bindId = x, _bindLabel = bindLabel bind} tx t)
cgen env (TApp e typ l) = do
  (c, RForall (TV alpha) t) <- cgen env e
  tHat <- fresh typ l
  pure (c, substReftReft1 tHat alpha t)
cgen env (TAbs tvar e _) = do
  (c, t) <- cgen env e
  pure (c, RForall tvar t)

single :: (Predicate r) => Env r a -> Id -> Fresh (RType r a)
single env x = case lookup x env of
  Just (RBase (Bind _ l) baseType _) -> do
  -- `x` is already bound, so instead of "re-binding" x we should selfify
  -- (al la Ou et al. IFIP TCS '04)
    v <- refreshId "VV#"
    pure $ RBase (Bind v l) baseType (varsEqual v x)
  Just rt -> pure rt
  Nothing -> error $ "Unbound Variable " ++ show x

fresh :: (Predicate r) => Type -> a -> Fresh (RType r a)
fresh typ l = go [] typ
  where
    go _ (TVar alpha) = pure $ RTVar alpha
    go env TUnit = freshBaseType env TUnit l
    go env TInt = freshBaseType env TInt l
    go env TBool = freshBaseType env TBool l
    go env (typ1 :=> typ2) = do
      rtype1 <- go env typ1
      x <- refreshId "karg#"
      rtype2 <- go ((x,typ1):env) typ2
      pure $ RFun (Bind x l) rtype1 rtype2
    go _env (TCtor _ctor _types) = error "TODO: fresh at constructor type. Same as base type?"
    go env (TForall tvar typ) = do
      rtype <- go env typ
      pure $ RForall tvar rtype

freshBaseType :: (Predicate r) => [(Id, Type)] -> Type -> a -> Fresh (RType r a)
freshBaseType env baseType l = do
  kappa <- refreshId "kvar#"
  v <- refreshId "VV#"
  let k = buildKvar kappa (v:(map fst env))
  pure $ RBase (Bind v l) baseType k

sub :: (Predicate r) => RType r a -> RType r a -> Constraint r
sub (RBase (Bind x1 _) b1 p1) (RBase (Bind x2 _) b2 p2)
  | b1 == b2 = All x1 b1 p1 (Head $ varSubst x1 x2 p2) -- TODO: check whether the guard is correct/needed
  | otherwise = error "error?"
sub (RFun (Bind x _) s s') (RFun (Bind y _) t t') = CAnd [c, generalizedImplication y t c']
  where
    c = sub t s
    c' = sub (substReftPred1 y x s') t'
sub (RTVar alpha) (RTVar beta)
  | alpha == beta = Head true
  | otherwise = error "Constraint generation subtyping error"
sub (RForall alpha t1) (RForall beta t2)
  | alpha == beta = sub t1 t2
  | otherwise = error "Constraint generation subtyping error"
sub _ _ = error "CGen subtyping error"

-- | (x :: t) => c
generalizedImplication :: (Predicate r) => Id -> (RType r a) -> Constraint r -> Constraint r
generalizedImplication x (RBase (Bind y _) b p) c = All x b (varSubst x y p) c
generalizedImplication _ _ c = c
