{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE BangPatterns #-}

--------------------------------------------------------------------------------
-- | This module generates refinement type constraints
-- | (see Cosman and Jhala, ICFP '17)
--------------------------------------------------------------------------------

module Language.Mist.CGen
  ( generateConstraints
  , NNF (..)
  ) where

import Language.Mist.Types
import Language.Mist.Names
import Data.Bifunctor (second)

-------------------------------------------------------------------------------
-- Data Structures
-------------------------------------------------------------------------------
type Env r a = [(Id, RType r a)]

type CGenConstraints r a = (Predicate r, Show r, Show a, PPrint r, Eq r)

-------------------------------------------------------------------------------
-- | generateConstraints is our main entrypoint to this module
-------------------------------------------------------------------------------
generateConstraints :: CGenConstraints r a => ElaboratedExpr r a -> NNF r
generateConstraints = fst . runFresh . synth []

synth :: CGenConstraints r a =>
        Env r a -> ElaboratedExpr r a -> Fresh (NNF r, RType r a)
synth env e = do
  -- !_ <- traceM $ show ("synth", pprint e)
  _synth env e

_synth :: CGenConstraints r a =>
        Env r a -> ElaboratedExpr r a -> Fresh (NNF r, RType r a)
_synth _ e@Unit{}    = (Head true,) <$> prim e
_synth _ e@Number{}  = (Head true,) <$> prim e
_synth _ e@Boolean{} = (Head true,) <$> prim e
_synth _ e@Prim{}    = (Head true,) <$> prim e
_synth env (Id x _)  = (Head true,) <$> single env x

-- TODO: check that this rule is correct. In particular the interaction of rebindInEnv generated constraints and mkAll. I think it should be fine due to how single works.
_synth env (If (Id y _) e1 e2 l) = do
  idT <- refreshId ("then:"<>y)
  idF <- refreshId ("else:"<>y)
  -- TODO make these check, after pulling the right thing out of l
  (c1, t1) <- synth env e1
  (c2, t2) <- synth env e2
  tHat <- fresh l env (eraseRType t1) -- could just as well be t2
  cSub1 <- t1 <: tHat
  cSub2 <- t2 <: tHat
  let c = CAnd [All idT TBool (var y) (CAnd [c1, cSub1]),
                All idF TBool (varNot y) (CAnd [c2, cSub2])]
  pure (c, tHat)
_synth _ If{} = error "INTERNAL ERROR: if not in ANF"

-- TODO: recursive let?
_synth env (Let b e1 e2 loc) = do
  (c, tx, c', rtype) <- go b
  tHat <- fresh loc env (eraseRType rtype)
  cSub <- rtype <: tHat
  let cs = (if c == CAnd [] then [] else [c]) ++ [mkAll (bindId b) tx (CAnd [c', cSub])]
  pure (CAnd cs, tHat)

  where
  -- go returns c, tx, c', rtype where
  -- c is the constraints from anything that shouldn't be under the generalized implication
  -- tx is the bound type
  -- c' is the constraints that should go under the generalized implication
  -- rtype is the synthesized type which will need to be guarded by fresh
  go (AnnBind x (Just (ElabAssume tx)) _) = do
    (c, t) <- synth ((x, tx): env) e2
    pure (CAnd [], tx, c, t)

  go (AnnBind x (Just (ElabRefined rt@RIFun{})) _) = do
    let (ns, tx) = splitImplicits rt
    c1 <- check (ns ++ env) e1 tx
    let c1' = foldr (\(z, tz) c -> mkAll z tz c) c1 ns
    (c2, t2) <- synth ((x, rt):env) e2
    pure (c1', rt, c2, t2)

  go (AnnBind x (Just (ElabRefined tx)) _) = do
    c1 <- check env e1 tx
    (c2, t2) <- synth ((x, tx):env) e2
    pure (c1, tx, c2, t2)

  go (AnnBind x (Just (ElabUnrefined typ)) l) = do
    t1 <- fresh l env typ
    c1 <- check env e1 t1
    (c2, t2) <- synth ((x, t1):env) e2
    pure (c1, t1, c2, t2)

  go (AnnBind _ Nothing _) = error "INTERNAL ERROR: annotation missing on let"

_synth env (App e (Id y loc) _) = do
  (c, t) <- synth env e
  (c', t') <- appSynth env t y loc
  pure (CAnd [c, c'], t')

_synth _ App{} = error "argument is non-variable"

_synth _ (Lam (AnnBind _ Nothing _) _ _) = error "should not occur"
_synth _ (Lam (AnnBind _ (Just (ElabAssume _)) _) _ _) = error "should not occur"

_synth env (Lam (AnnBind x (Just (ElabRefined tx)) loc) e _) = do
  (c, t) <- synth ((x, tx):env) e
  pure (mkAll x tx c, RFun (Bind x loc) tx t)

_synth env (Lam (AnnBind x (Just (ElabUnrefined typ)) loc) e _) = do
  tHat <- fresh loc env typ
  (c, t) <- synth ((x, tHat):env) e
  pure (mkAll x tHat c, RFun (Bind x loc) tHat t)

_synth env (TApp e typ loc) = do
  (c, RForall (TV alpha) t) <- synth env e
  tHat <- fresh loc env typ
  pure (c, substReftReft (alpha |-> tHat) t)
_synth env (TAbs tvar e _) = do
  (c, t) <- synth env e
  pure (c, RForall tvar t)

appSynth :: CGenConstraints r a => Env r a -> RType r a -> Id -> a -> Fresh (NNF r, RType r a)
appSynth env t y loc = do
  -- !_ <- traceM $ show ("appSynth", pprint t, y)
  _appSynth env t y loc

-- | env | tfun ⊢ y >>
_appSynth :: CGenConstraints r a => Env r a -> RType r a -> Id -> a -> Fresh (NNF r, RType r a)
_appSynth env (RFun x tx t) y loc = do
  c <- check env (Id y loc) tx
  pure (c, substReftPred (bindId x |-> y) t)

_appSynth env (RIFun (Bind x _) tx t) y loc = do
  z <- refreshId x
  (c, t') <- appSynth ((z, tx):env) (substReftPred (x |-> z) t) y loc
  tHat <- fresh loc env (eraseRType t')
  c' <- t' <: tHat
  pure (mkExists z tx (CAnd [c, c']), tHat)

_appSynth _ _ _ _ = error "Applying non function"

single :: CGenConstraints r a => Env r a -> Id -> Fresh (RType r a)
single env x = case lookup x env of
  Just (RBase (Bind y l) baseType reft) -> do
  -- `x` is already bound, so instead of "re-binding" x we should selfify
  -- (al la Ou et al. IFIP TCS '04)
    v <- refreshId $ "VV" ++ cSEPARATOR
    pure $ RBase (Bind v l) baseType (strengthen (subst (y |-> v) reft) (varsEqual v x))
  Just rt -> pure rt
  Nothing -> error $ "Unbound Variable " ++ show x ++ show env


check :: CGenConstraints r a => Env r a -> ElaboratedExpr r a -> RType r a -> Fresh (NNF r)
check env e t = do
  -- !_ <- traceM $ show ("check", pprint e, pprint t)
  _check env e t

_check :: CGenConstraints r a => Env r a -> ElaboratedExpr r a -> RType r a -> Fresh (NNF r)
_check env (Let b e1 e2 _) t2
  -- Annotated with an assume
  | (AnnBind x (Just (ElabAssume tx)) _) <- b = do
    c <- check ((x, tx):env) e2 t2
    pure $ mkAll x tx c

  -- Annotated with an RType (Implicit Parameter)
  | (AnnBind x (Just (ElabRefined rt@RIFun{})) _) <- b = do
    let (ns, tx) = splitImplicits rt
    c1 <- check (ns ++ env) e1 tx
    let c = foldr (\(z, tz) c -> mkAll z tz c) c1 ns
    c2 <- check ((x, rt):env) e2 t2
    let c' = mkAll x rt c2
    pure $ CAnd [c, c']

  -- Annotated with an RType
  | (AnnBind x (Just (ElabRefined tx)) _) <- b = do
    c1 <- check env e1 tx
    c2 <- check ((x, tx):env) e2 t2
    let c' = mkAll x tx c2
    pure $ CAnd [c1, c']

  -- Unrefined
  | (AnnBind x (Just (ElabUnrefined typ)) loc) <- b = do
    tHat <- fresh loc env typ
    c1 <- check env e1 tHat
    c2 <- check ((x, tHat):env) e2 t2
    let c' = mkAll x tHat c2
    pure $ CAnd [c1, c']

  | (AnnBind _ Nothing _) <- b = error "INTERNAL ERROR: annotation missing on let"

-- TODO: check that this rule is correct. In particular the interaction of rebindInEnv generated constraints and mkAll. I think it should be fine due to how single works.
_check env (If (Id y _) e1 e2 _) t2 = do
  idT <- refreshId ("then:"<>y)
  idF <- refreshId ("else:"<>y)
  c1 <- check env e1 t2
  c2 <- check env e2 t2
  pure $ CAnd [All idT TBool (var y) c1,
               All idF TBool (varNot y) c2]
_check _ If{} _ = error "INTERNAL ERROR: if not in ANF"

_check env (App e (Id y loc) _) t = do
  (c, t') <- synth env e
  c' <- appCheck env t' y loc t
  pure $ CAnd [c, c']

-- this is INCORRECT for implicits
_check env e t = do
  (c, t') <- synth env e
  cSub <- t' <: t
  pure $ CAnd [c, cSub]

appCheck :: CGenConstraints r a => Env r a -> RType r a -> Id -> a -> RType r a -> Fresh (NNF r)
appCheck env t y loc t' = do
  -- !_ <- traceM $ show ("appCheck", pprint t, y)
  _appCheck env t y loc t'

-- | env | t ⊢ y << t'
_appCheck :: CGenConstraints r a => Env r a -> RType r a -> Id -> a -> RType r a -> Fresh (NNF r)
_appCheck env (RFun (Bind x _) tx t) y loc t' = do
  c <- check env (Id y loc) tx
  cSub <- substReftPred (x |-> y) t <: t'
  pure $ CAnd [c, cSub]

_appCheck env (RIFun (Bind x _) tx t) y loc t' = do
  z <- refreshId x
  c <- appCheck ((z, tx):env) (substReftPred (x |-> z) t) y loc t'
  pure $ mkExists z tx c

_appCheck _ _ _ _ _ = error "application at non function type"

fresh :: CGenConstraints r a => a -> Env r a -> Type -> Fresh (RType r a)
fresh l _ (TVar alpha) = do
  x <- refreshId $ "karg" ++ cSEPARATOR
  pure $ RBase (Bind x l) (TVar alpha) true
fresh loc env TUnit = freshBaseType loc env TUnit
fresh loc env TInt = freshBaseType loc env TInt
fresh loc env TBool = freshBaseType loc env TBool
fresh loc env (typ1 :=> typ2) = do
  rtype1 <- fresh loc env typ1
  x <- refreshId $ "karg" ++ cSEPARATOR
  rtype2 <- fresh loc ((x,rtype1):env) typ2
  pure $ RFun (Bind x loc) rtype1 rtype2
fresh l env (TCtor ctor types) = do -- TODO: reduce duplication with freshBaseType
  kappa <- refreshId $ "kvar" ++ cSEPARATOR
  v <- refreshId $ "VV" ++ cSEPARATOR
  let k = buildKvar kappa $ v : map fst (foTypes (eraseRTypes env))
  appType <- RApp ctor <$> mapM (sequence . second (fresh l env)) types
  pure $ RRTy (Bind v l) appType k
fresh l env (TForall tvar typ) = RForall tvar <$> fresh l env typ

freshBaseType :: (Predicate r) => a -> Env r a -> Type -> Fresh (RType r a)
freshBaseType l env baseType = do
  kappa <- refreshId $ "kvar" ++ cSEPARATOR
  v <- refreshId $ "VV" ++ cSEPARATOR
  let k = buildKvar kappa $ v : map fst (foTypes (eraseRTypes env))
  pure $ RBase (Bind v l) baseType k

-- filters out higher-order type binders in the environment
-- TODO(Matt): check that this is the correct behavior
foTypes :: [(Id, Type)] -> [(Id, Type)]
foTypes ((x, t@TVar{}):xs) = (x, t):foTypes xs
foTypes ((x, t@TUnit{}):xs) = (x, t):foTypes xs
foTypes ((x, t@TInt{}):xs) = (x, t):foTypes xs
foTypes ((x, t@TBool{}):xs) = (x, t):foTypes xs
foTypes ((_, _ :=> _):xs) = foTypes xs
foTypes ((_, TCtor{}):xs) = foTypes xs
foTypes ((_, TForall{}):xs) = foTypes xs
foTypes [] = []

eraseRTypes :: Env r a -> [(Id, Type)]
eraseRTypes = map (\(id, rtype) -> (id, eraseRType rtype))

(<:) :: CGenConstraints r a => RType r a -> RType r a -> Fresh (NNF r)
rtype1 <: rtype2 = do
  -- !_ <- traceM $ show ("<:", pprint rtype1, pprint rtype2)
  rtype1 <<: rtype2

(<<:) :: CGenConstraints r a => RType r a -> RType r a -> Fresh (NNF r)
rtype1 <<: rtype2 = go (flattenRType rtype1) (flattenRType rtype2)
  where
    go (RBase (Bind x1 _) b1 p1) (RBase (Bind x2 _) b2 p2)
      | b1 == b2 = pure $ All x1 b1 p1 (Head $ varSubst (x2 |-> x1) p2)
      | otherwise = error $ "error?" ++ show b1 ++ show b2
    go (RFun (Bind x1 _) t1 t1') (RFun (Bind x2 _) t2 t2') = do
      c <- t2 <: t1
      c' <- substReftPred (x1 |-> x2) t1' <: t2'
      pure $ CAnd [c, mkAll x2 t2 c']
    go (RForall alpha t1) (RForall beta t2)
      | alpha == beta = t1 <: t2
      | otherwise = error "Constraint generation subtyping error"
    go (RApp c1 vts1) (RApp c2 vts2)
      | c1 == c2  = CAnd <$> sequence (concat $ zipWith constructorSub vts1 vts2)
      | otherwise = error "CGen: constructors don't match"
    go (RIFun (Bind x _) t1 t1') t2 = do
      z <- refreshId x
      cSub <- substReftPred (x |-> z) t1' <: t2
      pure $ mkExists z t1 cSub
    go (RRTy (Bind x1 _) rt1 p1) (RRTy (Bind x2 _) rt2 p2) = do
      let outer = All x1 (eraseRType rt1) p1 (Head $ varSubst (x2 |-> x1) p2)
      inner <- rt1 <: rt2
      pure $ CAnd [outer, inner]
    go _ _ = error $ "CGen subtyping error. Got:\n\n" ++ show rtype1 ++ "\n\nbut expected:\n\n" ++ show rtype2 ++ "\n"

(v, rt1) `constructorSub` (_,rt2) = case v of
                         -- TODO: write tests that over these two cases...
                         Invariant -> []
                         Bivariant -> [rt1 <: rt2, rt2 <: rt1]
                         Covariant -> [rt1 <: rt2]
                         Contravariant -> [rt2 <: rt1]

flattenRType :: CGenConstraints r a => RType r a -> RType r a
flattenRType rrty@(RRTy (Bind x _) rt p)
  | (RBase by typ p') <- rt = RBase by typ (strengthen p' (varSubst (x |-> bindId by) p))
  | (RRTy by rt' p') <- rt = flattenRType (RRTy by rt' (strengthen p' (varSubst (x |-> bindId by) p)))
  | otherwise = rrty
flattenRType rt = rt


-- TODO: RApp?
-- | (x :: t) => c
mkAll :: CGenConstraints r a => Id -> RType r a -> NNF r -> NNF r
mkAll x rt c = case flattenRType rt of
   RBase (Bind y _) b p -> All x b (varSubst (y |-> x) p) c
   _ -> c

-- | ∃ x :: t. c
mkExists x rt c = case flattenRType rt of
             RBase (Bind y _) b p -> Any x b (varSubst (y |-> x) p) c
             _ -> c

splitImplicits :: RType r a -> ([(Id, RType r a)], RType r a)
splitImplicits (RIFun b t t') = ((bindId b,t):bs, t'')
    where (bs,t'') = splitImplicits t'
splitImplicits rt = ([],rt)


