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

import Language.Mist.Types
import Language.Mist.Names

-------------------------------------------------------------------------------
-- Data Structures
-------------------------------------------------------------------------------
type Env r a = [(Id, RType r a)]

-------------------------------------------------------------------------------
-- | generateConstraints is our main entrypoint to this module
-------------------------------------------------------------------------------
generateConstraints :: (Predicate r) => AnfExpr (ElaboratedType r a) a -> Constraint r
generateConstraints = fst . runFresh . cgen []

cgen :: (Predicate r) =>
        Env r a -> AnfExpr (ElaboratedType r a) a -> Fresh (Constraint r, RType r a)
cgen _ e@Unit{} = (Head true,) <$> prim e
cgen _ e@Number{} = (Head true,) <$> prim e
cgen _ e@Boolean{} = (Head true,) <$> prim e
cgen _ e@Prim2{} = (Head true,) <$> prim e -- TODO: should this be a lookup?
                                      -- how should prims be handled?
cgen env (Id x _) = (Head true,) <$> single env x
cgen _env (If _e1 _e2 _e3 _) = error "TODO"

-- TODO: recursive let?
-- TODO: this implementation of let differs significantly from the paper: is it correct?
cgen env (Let bind@AnnBind{_aBindType = Just (Left tx)} e1 e2 _) = do
  let x = bindId bind
  (c1, t1) <- cgen env e1
  (c2, t2) <- cgen ((x, tx):env) e2
  tHat <- fresh (eraseRType t2) (extract e2)
  let c = generalizedImplication x tx (CAnd [c2, t2 `sub` tHat])
  pure (CAnd [c1, (t1 `sub` tx), c], tHat)
cgen env (Let bind e1 e2 _) = do
  let x = bindId bind
  (c1, t1) <- cgen env e1
  (c2, t2) <- cgen ((x, t1):env) e2
  tHat <- fresh (eraseRType t2) (extract e2)
  let c = generalizedImplication x t1 (CAnd [c2, t2 `sub` tHat])
  pure (CAnd [c1, c], tHat)

cgen env (App e (Id y _) _) = do
  (c, RFun x t t') <- cgen env e
  ty <- single env y
  let cy = ty `sub` t
  pure (CAnd [c, cy], substReftPred1 y (bindId x) t')
cgen _ (App _ _ _) = error "argument is non-variable"
cgen _env (Lam _bind@AnnBind{_aBindType = Nothing} _e _) = error "should not occur"
cgen env (Lam bind@AnnBind{_aBindType = Just (Right typ)} e _) = do
  let x = bindId bind
  tHat <- fresh typ (bindLabel bind)
  (c, t) <- cgen ((x, tHat):env) e
  pure (generalizedImplication x tHat c, RFun Bind{_bindId = x, _bindLabel = bindLabel bind} tHat t)
cgen env (Lam bind@AnnBind{_aBindType = Just (Left tx)} e _) = do
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
    v <- refreshId $ "VV" ++ cSEPARATOR
    pure $ RBase (Bind v l) baseType (varsEqual v x)
  Just rt -> pure rt
  Nothing -> error $ "Unbound Variable " ++ show x

fresh :: (Predicate r) => Type -> a -> Fresh (RType r a)
fresh typ l = go [] typ
  where
    go _ (TVar alpha) = do
      x <- refreshId $ "karg" ++ cSEPARATOR
      pure $ RBase (Bind x l) (TVar alpha) true
    go env TUnit = freshBaseType env TUnit l
    go env TInt = freshBaseType env TInt l
    go env TBool = freshBaseType env TBool l
    go env (typ1 :=> typ2) = do
      rtype1 <- go env typ1
      x <- refreshId $ "karg" ++ cSEPARATOR
      rtype2 <- go ((x,typ1):env) typ2
      pure $ RFun (Bind x l) rtype1 rtype2
    go _env (TCtor _ctor _types) = error "TODO: fresh at constructor type. Same as base type?"
    go env (TForall tvar typ) = do
      rtype <- go env typ
      pure $ RForall tvar rtype

freshBaseType :: (Predicate r) => [(Id, Type)] -> Type -> a -> Fresh (RType r a)
freshBaseType env baseType l = do
  kappa <- refreshId $ "kvar" ++ cSEPARATOR
  v <- refreshId $ "VV" ++ cSEPARATOR
  let k = buildKvar kappa (v:(map fst env))
  pure $ RBase (Bind v l) baseType k

sub :: (Predicate r) => RType r a -> RType r a -> Constraint r
sub rtype1 rtype2 = go (flattenRType rtype1) (flattenRType rtype2)
  where
    go (RBase (Bind x1 _) b1 p1) (RBase (Bind x2 _) b2 p2)
      | b1 == b2 = All x1 b1 p1 (Head $ varSubst x1 x2 p2) -- TODO: check whether the guard is correct/needed
      | otherwise = error "error?"
    go (RFun (Bind x _) s s') (RFun (Bind y _) t t') = CAnd [c, generalizedImplication y t c']
      where
        c = sub t s
        c' = sub (substReftPred1 y x s') t'
    go (RForall alpha t1) (RForall beta t2)
      | alpha == beta = sub t1 t2
      | otherwise = error "Constraint generation subtyping error"
    go _ _ = error $ "CGen subtyping error"

-- | (x :: t) => c
generalizedImplication :: (Predicate r) => Id -> RType r a -> Constraint r -> Constraint r
generalizedImplication x (RBase (Bind y _) b p) c = All x b (varSubst x y p) c
generalizedImplication _ _ c = c

flattenRType :: (Predicate r) => RType r a -> RType r a
flattenRType (RRTy b rtype reft) = strengthenRType (flattenRType rtype) b reft
flattenRType rtype = rtype

strengthenRType :: (Predicate r) => RType r a -> Bind a -> r -> RType r a
strengthenRType (RBase b t reft) b' reft' = RBase b t (strengthen reft renamedReft')
  where
    renamedReft' = varSubst (bindId b) (bindId b') reft'
strengthenRType (RFun _ _ _) _ _ = error "TODO"
strengthenRType (RRTy b rtype reft) b' reft' = RRTy b rtype (strengthen reft renamedReft')
  where
    renamedReft' = varSubst (bindId b) (bindId b') reft'
strengthenRType (RForall _ _) _ _ = error "TODO"
