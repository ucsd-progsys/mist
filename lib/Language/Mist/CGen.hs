{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE BangPatterns #-}
{-# OPTIONS_GHC "-fmax-pmcheck-iterations=10000000" #-}

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

import Debug.Trace (traceM)

-------------------------------------------------------------------------------
-- Data Structures
-------------------------------------------------------------------------------
type Env r a = [(Id, RType r a)]

type CGenConstraints r e a = (Located a, Predicate r e, Show r, Show a, PPrint r, Eq r, Show e)

-------------------------------------------------------------------------------
-- | generateConstraints is our main entrypoint to this module
-------------------------------------------------------------------------------
generateConstraints :: CGenConstraints r e a => ElaboratedExpr r a -> NNF r
generateConstraints = fst . runFresh . synth []

synth :: CGenConstraints r e a =>
        Env r a -> ElaboratedExpr r a -> Fresh (NNF r, RType r a)
synth env e = do
  (c, outT) <- _synth env e
  -- !_ <- traceM $ "synth: " <> "⊢  " <> pprint e <> "\n\t => " <> pprint outT <> "\n\t ⊣ " <> show c <> "\n\n"
  pure (c, outT)

_synth :: CGenConstraints r e a =>
        Env r a -> ElaboratedExpr r a -> Fresh (NNF r, RType r a)
_synth _ e@Unit{} = (Head (sourceSpan e) true,) <$> prim e
_synth _ e@Number{} = (Head (sourceSpan e) true,) <$> prim e
_synth _ e@Boolean{} = (Head (sourceSpan e) true,) <$> prim e
_synth _ e@Prim{} = (Head (sourceSpan e) true,) <$> prim e
_synth env e@(Id x _) = (Head (sourceSpan e) true,) <$> single env x

-- _synth env (If e1 e2 e3 l) -- TODO: put this back
--   | Just cond <- interp e1 = do
--     idT <- refreshId "then:"
--     idF <- refreshId "else:"
--     (c1, t1) <- synth env e1
--     case t1 of
--       (RBase _ TBool _) -> pure ()
--       _ -> error "non bool condition"
--     (c2, t2) <- synth ((idT, t1):env) e2
--     (c3, t3) <- synth ((idF, t1):env) e3
--     -- TODO make these check, after pulling the right thing out of l
--     tHat <- fresh l env (eraseRType t2) -- could just as well be t2
--     cSub2 <- (t2 <: tHat) l
--     cSub3 <- (t3 <: tHat) l
--     let c = CAnd [ c1
--                  , All idT TBool (makePred cond) (CAnd [c2, cSub2])
--                  , All idF TBool (makePred $ exprNot cond) (CAnd [c3, cSub3]) ]
--     pure (c, tHat)

_synth env (If e1@(Id y _) e2 e3 l) = do -- TODO: put this back
    idT <- refreshId "then:"
    idF <- refreshId "else:"
    (c1, t1) <- synth env e1
    case t1 of
      (RBase _ TBool _) -> pure ()
      _ -> error "non bool condition"
    (c2, t2) <- synth ((idT, t1):env) e2
    (c3, t3) <- synth ((idF, t1):env) e3
    -- TODO make these check, after pulling the right thing out of l
    tHat <- freshRType l env t2 -- could just as well be t2
    cSub2 <- (t2 <: tHat) l
    cSub3 <- (t3 <: tHat) l
    let c = CAnd [ c1
                 , All idT TBool (makePred (var y)) (CAnd [c2, cSub2])
                 , All idF TBool (makePred $ exprNot (var y)) (CAnd [c3, cSub3]) ]
    pure (c, tHat)

_synth env (If e1 e2 e3 l) = do
  condVar <- refreshId "cond"
  (c1, t1) <- synth env e1
  let (y, cond) =
        case t1 of
          (RBase (Bind y _) TBool cond) -> (y, cond)
          _ -> error "non bool condition"
  (c2, t2) <- synth ((condVar, t1):env) e2
  (c3, t3) <- synth ((condVar, t1):env) e3
  -- TODO make these check, after pulling the right thing out of l
  tHat <- freshRType l env t2 -- could just as well be t2
  cSub2 <- (t2 <: tHat) l
  cSub3 <- (t3 <: tHat) l
  let cond' = varSubstP (y |-> condVar) cond
  let c = CAnd [ c1
                , All condVar TBool (strengthen (makePred $ var condVar) cond')
                  (CAnd [c2, cSub2])
                , All condVar TBool (strengthen (makePred $ exprNot $ var condVar) cond')
                  (CAnd [c3, cSub3]) ]
  pure (c, tHat)

_synth env (Unpack (Bind x _) (Bind y _) e1 e2 loc) = do
  (c1, tSigma) <- synth env e1
  let (tx, ty) = case tSigma of
        RIExists (Bind x' _) tx ty -> (tx, (substReftPred (x' |-> x) ty))
        _ -> error "unpacking non-sigma type"
  (c2, rtype) <- synth ((x, tx):(y, ty):env) e2
  tHat <- freshRType loc env rtype
  cSub <- (rtype <: tHat) loc
  pure (CAnd [c1, mkAll x tx (mkAll y ty (CAnd [c2, cSub]))], tHat)

_synth env (Let b e1 e2 loc) = do
  (tx, c, rtype) <- go b
  tHat <- freshRType loc env rtype
  cSub <- (rtype <: tHat) loc
  pure (mkAll (bindId b) tx (CAnd [c, cSub]), tHat)

  where
  -- go returns tx, c, rtype where
  -- tx is the bound type
  -- c is the constraints that should go under the generalized implication
  -- rtype is the synthesized type which will need to be guarded by fresh
  go (AnnBind x (Just (ElabAssume tx)) _) = do
    (c, t) <- synth ((x, tx): env) e2
    pure (tx, c, t)

  go (AnnBind x (Just (ElabRefined tx)) _) = do
    c1 <- check ((x, tx):env) e1 tx
    (c2, t2) <- synth ((x, tx):env) e2
    pure (tx, CAnd [c1, c2], t2)

  -- Unrefined
  -- Not allowed to be recursive
  go (AnnBind x (Just (ElabUnrefined typ)) l) = do
    t1 <- fresh l env typ
    c1 <- check env e1 t1
    (c2, t2) <- synth ((x, t1):env) e2
    pure (t1, CAnd [c1, c2], t2)

  go (AnnBind _ Nothing _) = error "INTERNAL ERROR: annotation missing on let"

_synth env (App e1 e2 _) = do
  (c, t) <- synth env e1
  (c', t') <- appSynth env t e2
  pure (CAnd [c, c'], t')

_synth _ (Lam (AnnBind _ Nothing _) _ _) = error "should not occur"
_synth _ (Lam (AnnBind _ (Just (ElabAssume _)) _) _ _) = error "should not occur"

_synth env (Lam (AnnBind x (Just (ElabRefined tx)) loc) e _) = do
  (c, t) <- synth ((x, tx):env) e
  pure (mkAll x tx c, RFun (Bind x loc) tx t)

_synth env (Lam (AnnBind x (Just (ElabUnrefined typ)) loc) e _) = do
  tHat <- fresh loc env typ
  (c, t) <- synth ((x, tHat):env) e
  pure (mkAll x tHat c, RFun (Bind x loc) tHat t)

-- TODO: ILam?

_synth env (TApp e typ loc) = do
  (c, scheme ) <- synth env e
  case scheme of
     RForall (TV alpha) t -> do
        tHat <- stale loc typ
        pure (c, substReftReft (alpha |-> tHat) t)
     RForallP (TV alpha) t -> do
        tHat <- fresh loc env typ
        pure (c, substReftReft (alpha |-> tHat) t)
     _ -> error "TApp on not-a-scheme"

_synth env (TAbs tvar e _) = do
  (c, t) <- synth env e
  pure (c, RForall tvar t)

stale :: CGenConstraints r e a => a -> Type -> Fresh (RType r a)
stale loc (TVar alpha) = do
  x <- refreshId $ "staleArg" ++ cSEPARATOR
  pure $ RBase (Bind x loc) (TVar alpha) true
stale loc TUnit = staleBaseType loc TUnit
stale loc TInt = staleBaseType loc TInt
stale loc TBool = staleBaseType loc TBool
stale loc (typ1 :=> typ2) = do
  rtype1 <- stale loc typ1
  x <- refreshId $ "staleArg" ++ cSEPARATOR
  rtype2 <- stale loc typ2
  pure $ RFun (Bind x loc) rtype1 rtype2
stale l (TCtor ctor types) = do -- TODO: reduce duplication with staleBaseType
  v <- refreshId $ "staleCtorVV" ++ cSEPARATOR
  appType <- RApp ctor <$> mapM (sequence . second (stale l)) types
  pure $ RRTy (Bind v l) appType true
stale l (TForall tvar typ) = RForall tvar <$> stale l typ

staleBaseType :: (Predicate r e) => a -> Type -> Fresh (RType r a)
staleBaseType l baseType = do
  v <- refreshId $ "staleBaseVV" ++ cSEPARATOR
  pure $ RBase (Bind v l) baseType true

appSynth :: CGenConstraints r e a => Env r a -> RType r a -> ElaboratedExpr r a -> Fresh (NNF r, RType r a)
appSynth env t e = do
  (c, outT) <- _appSynth env t e
  -- !_ <- traceM $ "appSynth: " <> pprint t <> "\n\t ⊢ " <> pprint e <> "\n\t >> " <> pprint outT
  pure (c, outT)

-- | env | tfun ⊢ y >>
_appSynth :: (CGenConstraints r e a) => Env r a -> RType r a -> ElaboratedExpr r a -> Fresh (NNF r, RType r a)
-- _appSynth env (RFun x tx t) e -- TODO fix substE and this
--   | Just reft <- interp e = do
--   c <- check env e tx
--   pure (c, substReftPredWith substE (bindId x |-> reft) t)

_appSynth env (RFun x tx t) e@(Id y _) = do
  c <- check env e tx
  pure (c, substReftPred (bindId x |-> y) t)

_appSynth env (RFun x tx t) e = do
  (c1, te) <- synth env e
  c2 <- (te <: tx) (sourceSpan e)
  tHat <- freshRType (extractLoc e) env t
  y <- refreshId "Y"
  c3 <- (substReftPred (bindId x |-> y) t <: tHat) (sourceSpan e)
  pure (CAnd [c1, c2, mkAll y te c3], tHat)

_appSynth env (RIFun (Bind x _) tx t) e = do
  z <- refreshId x
  (c, t') <- appSynth ((z, tx):env) (substReftPred (x |-> z) t) e
  tHat <- freshRType (extractLoc e) env t'
  c' <- (t' <: tHat) (sourceSpan e)
  pure (mkExists z tx (CAnd [c, c']), tHat)

_appSynth _ _ _ = error "Applying non function"

single :: CGenConstraints r e a => Env r a -> Id -> Fresh (RType r a)
single env x = case flattenRType <$> lookup x env of
  Just (RBase (Bind y l) baseType reft) -> do
  -- `x` is already bound, so instead of "re-binding" x we should selfify
  -- (al la Ou et al. IFIP TCS '04)
    v <- refreshId $ "singleVV" ++ cSEPARATOR
    pure $ RBase (Bind v l) baseType (strengthen (subst (y |-> v) reft) (makePred $ exprsEqual (var v) (var x)))
  Just (RRTy (Bind y l) rt reft) -> do
    v <- refreshId $ "singleRR" ++ cSEPARATOR
    pure $ RRTy (Bind v l) rt (strengthen (subst (y |-> v) reft) (makePred $ exprsEqual (var v) (var x)))
  Just rt -> pure rt
  Nothing -> error $ "Unbound Variable " ++ show x ++ show env


check :: CGenConstraints r e a => Env r a -> ElaboratedExpr r a -> RType r a -> Fresh (NNF r)
check env e t = do
  c <- _check env e t
  -- !_ <- traceM $ "check: " <> "⊢ " <> pprint e <> "\n\t <= " <> pprint t <> "\n\t ⊣ " <> show c <> "\n\n"
  pure c

_check :: CGenConstraints r e a => Env r a -> ElaboratedExpr r a -> RType r a -> Fresh (NNF r)
_check env (ILam (Bind x _) e _) (RIFun y ty t) =
  mkAll x ty <$> check ((x, ty):env) e (substReftPred (bindId y |-> x) t)
_check env e rt@RIFun{} = do
  let (ns, tx) = splitImplicits rt
  c1 <- check (ns ++ env) e tx
  pure $ foldr (\(z, tz) c -> mkAll z tz c) c1 ns

_check env (Unpack (Bind x _) (Bind y _) e1 e2 _) t = do
  (c1, tSigma) <- synth env e1
  let (tx, ty) = case tSigma of
        RIExists (Bind x' _) tx ty -> (tx, (substReftPred (x' |-> x) ty))
        _ -> error "unpacking non-sigma type"
  c2 <- check ((x, tx):(y, ty):env) e2 t
  pure $ CAnd [c1, mkAll x tx (mkAll y ty c2)]

_check env (Let b e1 e2 _) t2
  -- Annotated with an assume
  | (AnnBind x (Just (ElabAssume tx)) _) <- b = do
    c <- check ((x, tx):env) e2 t2
    pure $ mkAll x tx c

  -- Annotated with an RType
  | (AnnBind x (Just (ElabRefined tx)) _) <- b = do
    c1 <- check ((x, tx):env) e1 tx
    c2 <- check ((x, tx):env) e2 t2
    pure $ mkAll x tx (CAnd [c1, c2])

  -- Unrefined
  -- Not allowed to be recursive
  | (AnnBind x (Just (ElabUnrefined typ)) loc) <- b = do
    tHat <- fresh loc env typ
    c1 <- check env e1 tHat
    c2 <- check ((x, tHat):env) e2 t2
    pure $ CAnd [c1, mkAll x tHat c2]

  | (AnnBind _ Nothing _) <- b = error "INTERNAL ERROR: annotation missing on let"

-- _check env (If e1 e2 e3 _) t2 -- TODO: put this back. It doesn't work due to higher order applications being "interp-able" without being reflected or bound.
--   | Just cond <- interp e1 = do
--     idT <- refreshId "then:"
--     idF <- refreshId "else:"
--     (c1, t1) <- synth env e1
--     case t1 of
--       (RBase _ TBool _) -> pure ()
--       _ -> error "non bool condition"
--     c2 <- check ((idT, t1):env) e2 t2
--     c3 <- check ((idF, t1):env) e3 t2
--     pure $ CAnd [ c1
--                 , All idT TBool (makePred cond) c2
--                 , All idF TBool (makePred $ exprNot cond) c3 ]

_check env (If e1@(Id y _) e2 e3 _) t2 = do
    idT <- refreshId "then:"
    idF <- refreshId "else:"
    (c1, t1) <- synth env e1
    case t1 of
      (RBase _ TBool _) -> pure ()
      _ -> error "non bool condition"
    c2 <- check ((idT, t1):env) e2 t2
    c3 <- check ((idF, t1):env) e3 t2
    pure $ CAnd [ c1
                , All idT TBool (makePred $ var y) c2
                , All idF TBool (makePred $ exprNot (var y)) c3 ]

_check env (If e1 e2 e3 _) t2 = do
  condVar <- refreshId "cond"
  (c1, t1) <- synth env e1
  let (y, cond) =
        case t1 of
          (RBase (Bind y _) TBool cond) -> (y, cond)
          _ -> error "non bool condition"
  c2 <- check ((condVar, t1):env) e2 t2
  c3 <- check ((condVar, t1):env) e3 t2
  let cond' = varSubstP (y |-> condVar) cond
  let c = CAnd [ c1
                , All condVar TBool (strengthen (makePred $ var condVar) cond') c2
                , All condVar TBool (strengthen (makePred $ exprNot $ var condVar) cond') c3 ]
  pure c

_check _ (Lam (AnnBind _ (Just (ElabAssume _)) _) _ _) _ = pure (CAnd [])
_check env (Lam (AnnBind x _ _) e _) (RFun y ty t) =
  mkAll x ty <$> check ((x, ty):env) e (substReftPred (bindId y |-> x) t)

_check env (TAbs tvar' e loc) (RForall (TV tvar) t)  = do
  stalert <- stale loc (TVar tvar')
  check env e (substReftReft (tvar |-> stalert) t)
_check env (TAbs tvar' e _) (RForallP (TV tvar) t) =
  check env e (substReftType (tvar |-> TVar tvar') t)

_check env (App e1 e2 _) t = do
  (c, t') <- synth env e1
  c' <- appCheck env t' e2 t
  pure $ CAnd [c, c']

_check env e t = do
  (c, t') <- synth env e
  cSub <- (t' <: t) (sourceSpan e)
  pure $ CAnd [c, cSub]

appCheck :: CGenConstraints r e a => Env r a -> RType r a -> ElaboratedExpr r a -> RType r a -> Fresh (NNF r)
appCheck env t e t' = do
  c <- _appCheck env t e t'
  -- !_ <- traceM $ "appCheck: " <> pprint t <> "\n\t ⊢ " <> pprint e <> "\n\t << " <> pprint t' <> "\n\t ⊣ " <> show c <> "\n\n"
  pure c

-- | env | t ⊢ y << t'
_appCheck :: CGenConstraints r e a => Env r a -> RType r a -> ElaboratedExpr r a -> RType r a -> Fresh (NNF r)
-- _appCheck env (RFun (Bind x _) tx t) e t' -- TODO: get this and substE working properly
--   | Just reft <- interp e = do
--   c <- check env e tx
--   cSub <- (substReftPredWith substE (x |-> reft) t <: t') (sourceSpan e)
--   pure $ CAnd [c, cSub]
_appCheck env (RFun (Bind x _) tx t) e@(Id y _) t' = do -- TODO: get this and substE working properly
  c <- check env e tx
  cSub <- (substReftPred (x |-> y) t <: t') (sourceSpan e)
  pure $ CAnd [c, cSub]
_appCheck env (RFun (Bind x _) tx t) e t' = do
  (c1, te) <- synth env e
  c2 <- (te <: tx) (sourceSpan e)
  y <- refreshId "Y"
  c3 <- (substReftPred (x |-> y) t <: t') (sourceSpan e)
  pure $ CAnd [c1, c2, mkAll y te c3]

_appCheck env (RIFun (Bind x _) tx t) e t' = do
  z <- refreshId x
  c <- appCheck ((z, tx):env) (substReftPred (x |-> z) t) e t'
  pure $ mkExists z tx c

_appCheck _ _ _ _ = error "application at non function type"

fresh :: CGenConstraints r e a => a -> Env r a -> Type -> Fresh (RType r a)
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
  v <- refreshId $ "freshCtorVV" ++ cSEPARATOR
  let k = buildKvar kappa $ v : map fst (foTypes (eraseRTypes env))
  appType <- RApp ctor <$> mapM (sequence . second (fresh l env)) types
  pure $ RRTy (Bind v l) appType k
fresh l env (TForall tvar typ) = RForall tvar <$> fresh l env typ

freshBaseType :: (Predicate r e) => a -> Env r a -> Type -> Fresh (RType r a)
freshBaseType l env baseType = do
  kappa <- refreshId $ "kvar" ++ cSEPARATOR
  v <- refreshId $ "freshBaseVV" ++ cSEPARATOR
  let k = buildKvar kappa $ v : map fst (foTypes (eraseRTypes env))
  pure $ RBase (Bind v l) baseType k

freshRType :: CGenConstraints r e a => a -> Env r a -> RType r a -> Fresh (RType r a)
freshRType l env (RIExists (Bind x _) tx ty) = do
  x' <- refreshId x
  RIExists (Bind x' l) <$> freshRType l env tx <*> freshRType l ((x',tx):env) ty
freshRType l env rtype = fresh l env (eraseRType rtype)

-- filters out higher-order type binders in the environment
-- TODO(Matt): check that this is the correct behavior
foTypes :: [(Id, Type)] -> [(Id, Type)]
foTypes ((x, t@TVar{}):xs) = (x, t):foTypes xs
foTypes ((x, t@TUnit{}):xs) = (x, t):foTypes xs
foTypes ((x, t@TInt{}):xs) = (x, t):foTypes xs
foTypes ((x, t@TBool{}):xs) = (x, t):foTypes xs
foTypes ((x, t@(TCtor (CT "Set") _)):xs) = (x,t):foTypes xs
foTypes ((_, _ :=> _):xs) = foTypes xs
foTypes ((_, TCtor{}):xs) = foTypes xs
foTypes ((_, TForall{}):xs) = foTypes xs
foTypes [] = []

eraseRTypes :: Env r a -> [(Id, Type)]
eraseRTypes = map (\(id, rtype) -> (id, eraseRType rtype))

(<:) :: (CGenConstraints r e a, Located b) => RType r a -> RType r a -> b -> Fresh (NNF r)
(<:) rtype1 rtype2 locable = do
  c <- (rtype1 <<: rtype2) locable
  -- !_ <- traceM $ "subtyping: " <> "⊢ " <> pprint rtype1 <> "\n\t<: " <> pprint rtype2 <> "\n\t⊣  " <> show c <> "\n\n"
  pure c

(<<:) :: (CGenConstraints r e a, Located b) => RType r a -> RType r a -> b -> Fresh (NNF r)
(<<:) rtype1 rtype2 locable = go (flattenRType rtype1) (flattenRType rtype2)
  where
    go :: (CGenConstraints r e a) => RType r a -> RType r a -> Fresh (NNF r)
    go (RBase (Bind x1 _) b1 p1) (RBase (Bind x2 _) b2 p2)
      | b1 == b2 = pure $ All x1 b1 p1 (Head (sourceSpan locable) $ varSubstP (x2 |-> x1) p2)
      | otherwise = error $ "error?" ++ show b1 ++ show b2
    go (RFun (Bind x1 _) t1 t1') (RFun (Bind x2 _) t2 t2') = do
      c <- (t2 <: t1) locable
      c' <- (substReftPred (x1 |-> x2) t1' <: t2') locable
      pure $ CAnd [c, mkAll x2 t2 c']
    go (RForall alpha t1) (RForall beta t2) =
      (t1 <: (substReftType ((unTV beta) |-> (TVar alpha)) t2)) locable
    go (RForallP alpha t1) (RForallP beta t2) =
      (t1 <: (substReftType ((unTV beta) |-> (TVar alpha)) t2)) locable
    go (RApp c1 vts1) (RApp c2 vts2)
      | c1 == c2  = CAnd <$> sequence (concat $ zipWith (constructorSub locable) vts1 vts2)
      | otherwise = error "CGen: constructors don't match"
    go t1 (RIFun (Bind x _) t2 t2') = do
      z <- refreshId x
      cSub <- (t1 <: substReftPred (x |-> z) t2') locable
      pure $ mkAll z t2 cSub
    go (RIFun (Bind x _) t1 t1') t2 = do
      z <- refreshId x
      cSub <- (substReftPred (x |-> z) t1' <: t2) locable
      pure $ mkExists z t1 cSub
    go (RIExists (Bind x1 _) t1 t1') (RIExists (Bind x2 _) t2 t2') = do
      c1 <- (t1 <: t2) locable
      c2 <- (t1' <: substReftPred (x2 |-> x1) t2') locable
      pure $ CAnd [c1, mkAll x1 t2 c2]
    go (RIExists (Bind x _) t1 t1') t2 = do
      z <- refreshId x
      cSub <- (substReftPred (x |-> z) t1' <: t2) locable
      pure $ mkAll z t1 cSub
    go t1 (RIExists (Bind x _) t2 t2') = do
      z <- refreshId x
      cSub <- (t1 <: substReftPred (x |-> z) t2') locable
      pure $ mkExists z t2 cSub
    go (RRTy (Bind x1 _) rt1 p1) (RRTy (Bind x2 _) rt2 p2) = do
      let outer = All x1 (eraseRType rt1) p1 (Head (sourceSpan locable) $ varSubstP (x2 |-> x1) p2)
      inner <- (rt1 <: rt2) locable
      pure $ CAnd [outer, inner]
    go rt1 (RRTy (Bind x _) rt2 reft) = do
      let (y,r) = rtsymreft rt1
      let subreft = All y (eraseRType rt1) r (Head (sourceSpan locable) $ varSubstP (x |-> y) reft)
      inner <- (rt1 <: rt2) locable
      pure $ CAnd [inner, subreft]
    go (RRTy (Bind x _) rt1 reft) rt2 = All x (eraseRType rt1) reft <$> (rt1 <: rt2) locable
    go _ _ = error $ "CGen subtyping error. Got:\n\n" ++ pprint rtype1 ++ "\n\nbut expected:\n\n" ++ pprint rtype2 ++ "\n" ++ "i.e. Got:\n\n" ++ pprint (eraseRType rtype1) ++ "\n\nbut expected:\n\n" ++ pprint (eraseRType rtype2) ++ "\n"

constructorSub locable (v, rt1) (_,rt2) = case v of
  -- TODO: write tests that over these two cases...
  Invariant -> []
  Bivariant -> [(rt1 <: rt2) locable, (rt2 <: rt1) locable]
  Covariant -> [(rt1 <: rt2) locable]
  Contravariant -> [(rt2 <: rt1) locable]

rtsymreft :: Predicate r e => RType r a -> (Id, r)
rtsymreft (RBase (Bind x _) _ r) = (x,r)
rtsymreft (RRTy (Bind x _) _ r) = (x,r)
rtsymreft _ = ("_",true)

flattenRType :: CGenConstraints r e a => RType r a -> RType r a
flattenRType rrty@(RRTy (Bind x _) rt p)
  | (RBase by typ p') <- rt = RBase by typ (strengthen p' (varSubstP (x |-> bindId by) p))
  | (RRTy by rt' p') <- rt = flattenRType (RRTy by rt' (strengthen p' (varSubstP (x |-> bindId by) p)))
  | otherwise = rrty
flattenRType rt = rt

-- TODO: RApp?
-- | (x :: t) => c
mkAll :: CGenConstraints r e a => Id -> RType r a -> NNF r -> NNF r
mkAll x rt c = case flattenRType rt of
   RBase (Bind y _) b p -> All x b (varSubstP (y |-> x) p) c
   RRTy (Bind y _) rt p -> All x (eraseRType rt) (varSubstP (y |-> x) p) c
   _ -> c

-- | ∃ x :: t. c
mkExists x rt c = case flattenRType rt of
             RBase (Bind y _) b p -> Any x b (varSubstP (y |-> x) p) c
             RRTy (Bind y _) rt p -> Any x (eraseRType rt) (varSubstP (y |-> x) p) c
             _ -> c

splitImplicits :: RType r a -> ([(Id, RType r a)], RType r a)
splitImplicits (RIFun b t t') = ((bindId b,t):bs, t'')
    where (bs,t'') = splitImplicits t'
splitImplicits rt = ([],rt)
