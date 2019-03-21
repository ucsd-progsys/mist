{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PatternGuards #-}

--------------------------------------------------------------------------------
-- | This module generates refinement type constraints
-- | (see Cosman and Jhala, ICFP '17)
--------------------------------------------------------------------------------

module Language.Mist.CGen
  ( generateConstraints
  , NNF (..)
  ) where

-- TODO: Do we need to run a Uniqify pass before we run this module?
-- Matt: We should uniquify at the beginning and then maintain the unique names property

import Language.Mist.Types
import Language.Mist.Names
import qualified Data.Map.Strict as M

-------------------------------------------------------------------------------
-- Data Structures
-------------------------------------------------------------------------------
type Env r a = [(Id, RType r a)]

-------------------------------------------------------------------------------
-- | generateConstraints is our main entrypoint to this module
-------------------------------------------------------------------------------
generateConstraints :: (Predicate r, Show r, Show a) =>
                       ElaboratedExpr r a -> NNF r
generateConstraints = fst . runFresh . cgen []

cgen :: (Predicate r, Show r, Show a) =>
        Env r a -> ElaboratedExpr r a -> Fresh (NNF r, RType r a)
cgen _ e@Unit{}    = (Head true,) <$> prim e
cgen _ e@Number{}  = (Head true,) <$> prim e
cgen _ e@Boolean{} = (Head true,) <$> prim e
cgen _ e@Prim{}    = (Head true,) <$> prim e
cgen env (Id x _)  = (Head true,) <$> single env x

cgen env (If (Id y _) e1 e2 l) = do
    rtT <- pure $ RBase (Bind idT l) TBool $ var y
    rtF <- pure $ RBase (Bind idF l) TBool $ varNot y
    (c1, t1) <- cgen ((idT,rtT):env) e1
    (c2, t2) <- cgen ((idF,rtF):env) e2
    tHat <- fresh l (foBinds env) (eraseRType t1) -- could just as well be t2
    let c = CAnd [mkAll idT rtT (CAnd [c1, t1 <: tHat]),
                  mkAll idF rtF (CAnd [c2, t2 <: tHat])]
    pure (c, tHat)
  where idT = y<>"then"
        idF = y<>"else"
cgen _ (If _ _ _ _) = error "INTERNAL ERROR: if not in ANF"

-- TODO: recursive let?
cgen env (Let b e1 e2 _)
  -- Annotated with an RType (Implicit Parameter)
  | (AnnBind x (Just (ElabRefined rt@(RIFun {}))) _) <- b = do
 let (ns, tx) = splitImplicits rt
 (c1, t1) <- cgen (ns ++ env) e1
 (c2, t2) <- cgen ((x, rt):env) e2
 tHat <- fresh (extractLoc e2) (foBinds env) (eraseRType t2)
 let c = mkAll x tx (CAnd [c2, t2 <: tHat])
 let c' = foldr (uncurry mkAll) (CAnd [c1, t1 <: tx]) ns
 pure (CAnd [c, c'], tHat)
  -- Annotated with an RType
  | (AnnBind x (Just (ElabRefined tx)) _) <- b = do
 (c1, t1) <- cgen env e1
 (c2, t2) <- cgen ((x, tx):env) e2
 tHat <- fresh (extractLoc e2) (foBinds env) (eraseRType t2)
 let c = mkAll x tx (CAnd [c2, t2 <: tHat])
 pure (CAnd [c1, c, t1 <: tx], tHat)
  -- Unrefined
  | (AnnBind x _ _) <- b = do
 (c1, t1) <- cgen env e1
 (c2, t2) <- cgen ((x, t1):env) e2
 tHat <- fresh (extractLoc e2) (foBinds env) (eraseRType t2)
 let c = mkAll x t1 (CAnd [c2, t2 <: tHat])
 pure (CAnd [c1, c], tHat)

cgen env (App e (Id y _) _) =
  cgen env e >>= \case
  (c, RFun x t t') -> do
    ty <- single env y
    let cy = ty <: t
    pure (CAnd [c, cy], substReftPred1 (bindId x) y t')
  (c, rit@RIFun{}) -> do
    let (ns, rt) = splitImplicits rit
    ns' <- sequence [ (,rt) <$> refreshId n | (n,rt) <- ns]
    let RFun x t t' = substReftPred (M.fromList $ zip (fst <$> ns') (fst <$> ns)) rt
    ty <- single env y
    tHat <- fresh (extractLoc e) (foBinds env) (eraseRType t')
    let cy = mkExists ns' $ CAnd [ty <: t, substReftPred1 (bindId x) y t'<: tHat]
    pure (CAnd [c, cy], tHat)
  _ -> error "CGen App failed"
-- there's a \forall fresh0##5 . true => c that's not being eliminated. We
-- could drop useless binds like this, but I want to see where it's being
-- generated here in the first place.
--
-- Seems it's the name given to the unused binder for Int -> ...



cgen _ (App _ _ _) = error "argument is non-variable"

cgen _ (Lam (AnnBind _ Nothing _) _ _) = error "should not occur"
cgen env (Lam (AnnBind x (Just (ElabRefined tx)) l) e _) = do
  (c, t) <- cgen ((x, tx):env) e
  pure (mkAll x tx c, RFun (Bind x l) tx t)

cgen env (Lam (AnnBind x (Just (ElabUnrefined typ)) l) e _) = do
  tHat <- fresh l (foBinds env) typ
  (c, t) <- cgen ((x, tHat):env) e
  pure (mkAll x tHat c, RFun (Bind x l) tHat t)

cgen env (TApp e typ l) = do
  (c, RForall (TV alpha) t) <- cgen env e
  tHat <- fresh l (foBinds env) typ
  pure (c, substReftReft1 tHat alpha t)
cgen env (TAbs tvar e _) = do
  (c, t) <- cgen env e
  pure (c, RForall tvar t)

single :: (Predicate r, Show a, Show r) => Env r a -> Id -> Fresh (RType r a)
single env x = case lookup x env of
  Just (RBase (Bind _ l) baseType _) -> do
  -- `x` is already bound, so instead of "re-binding" x we should selfify
  -- (al la Ou et al. IFIP TCS '04)
    v <- refreshId $ "VV" ++ cSEPARATOR
    pure $ RBase (Bind v l) baseType (varsEqual v x)
  Just rt -> pure rt
  Nothing -> error $ "Unbound Variable " ++ show x ++ show env

fresh l _ (TVar alpha) = do
  x <- refreshId $ "karg" ++ cSEPARATOR
  pure $ RBase (Bind x l) (TVar alpha) true
fresh l env TUnit = freshBaseType env TUnit l
fresh l env TInt = freshBaseType env TInt l
fresh l env TBool = freshBaseType env TBool l
fresh l env (typ1 :=> typ2) = do
  rtype1 <- (fresh l) env typ1
  x <- refreshId $ "karg" ++ cSEPARATOR
  rtype2 <- (fresh l) ((x,typ1):env) typ2
  pure $ RFun (Bind x l) rtype1 rtype2
fresh _l _env (TCtor _ctor _types) = error "TODO: fresh at constructor type. Same as base type?"
fresh l env (TForall tvar typ) = RForall tvar <$> (fresh l) env typ


freshBaseType :: (Predicate r) => [(Id, Type)] -> Type -> a -> Fresh (RType r a)
freshBaseType env baseType l = do
  kappa <- refreshId $ "kvar" ++ cSEPARATOR
  v <- refreshId $ "VV" ++ cSEPARATOR
  let k = buildKvar kappa $ v : map fst env
  pure $ RBase (Bind v l) baseType k

rtype1 <: rtype2 = go (flattenRType rtype1) (flattenRType rtype2)
  where
    go (RBase (Bind x1 _) b1 p1) (RBase (Bind x2 _) b2 p2)
      -- TODO: check whether the guard is correct/needed
      | b1 == b2 = All x1 b1 p1 (Head $ varSubst x1 x2 p2)
      | otherwise = error $ "error?" ++ show b1 ++ show b2
    go (RFun (Bind x _) s s') (RFun (Bind y _) t t') = CAnd [c, mkAll y t c']
      where
        c = t <: s
        -- ordering
        c' = substReftPred1 x y s' <: t'
    go (RForall alpha t1) (RForall beta t2)
      | alpha == beta = t1 <: t2
      | otherwise = error "Constraint generation subtyping error"
    go _ _ = error $ "CGen subtyping error. Got " ++ show rtype1 ++ " but expected " ++ show rtype2

-- | (x :: t) => c
mkAll :: (Predicate r) => Id -> RType r a -> NNF r -> NNF r
mkAll x rt c = case flattenRType rt of
                 (RBase (Bind y _) b p) -> All x b (varSubst x y p) c
                 _ -> c
mkExists xts c = foldr mkExi c xts
  where mkExi (x,rt) c = case flattenRType rt of
                             (RBase (Bind y _) b p) -> Any x b (varSubst x y p) c
                             _ -> c

foBinds [] = []
foBinds ((x, (RBase (Bind _ _) t _)):ts) = (x,t) : foBinds ts
foBinds (_:ts) = foBinds ts

flattenRType :: (Predicate r) => RType r a -> RType r a
flattenRType (RRTy b rtype reft) = strengthenRType (flattenRType rtype) b reft
flattenRType rtype = rtype

strengthenRType :: (Predicate r) => RType r a -> Bind t a -> r -> RType r a
strengthenRType (RBase b t reft) b' reft' = RBase b t (strengthen reft renamedReft')
  where
    renamedReft' = varSubst (bindId b) (bindId b') reft'
strengthenRType (RFun _ _ _) _ _ = error "TODO"
strengthenRType (RIFun _ _ _) _ _ = error "TODO"
strengthenRType (RRTy b rtype reft) b' reft' = RRTy b rtype (strengthen reft renamedReft')
  where
    renamedReft' = varSubst (bindId b) (bindId b') reft'
strengthenRType (RForall _ _) _ _ = error "TODO"


splitImplicits (RIFun b t t') = ((bindId b,t):bs, t'')
    where (bs,t'') = splitImplicits t'
splitImplicits rt = ([],rt)
