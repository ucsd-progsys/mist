{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE OverloadedStrings #-}
-- pattern checker isn't smart enough to check this file
{-# OPTIONS_GHC "-fno-warn-incomplete-patterns" #-}
{-# OPTIONS_GHC "-fno-warn-overlapping-patterns" #-}

module Language.Mist.ToFixpoint
  ( solve
  , exprToFixpoint
  , parsedExprPredToFixpoint
  ) where

import Data.String (fromString)
import Data.Bifunctor
import qualified Data.Map.Strict as MAP
import qualified Data.HashMap.Strict as HM
import Data.Maybe (fromMaybe)
import Data.List (intercalate)
import Text.Printf

import Language.Mist.Types as M
import qualified Language.Mist.Names as MN

import qualified Language.Fixpoint.Types.Config as C
import qualified Language.Fixpoint.Types as F
import qualified Language.Fixpoint.Smt.Theories as T
import qualified Language.Fixpoint.Horn.Types as HC
import qualified Language.Fixpoint.Horn.Solve as S

-- | Solves the subtyping constraints we got from CGen.

solve :: Measures -> NNF HC.Pred -> IO (F.Result (Integer, (String, SourceSpan)))
solve measures constraints = do
  S.solve cfg (HC.Query [] (collectKVars fixpointConstraint) fixpointConstraint (measureHashMap measures) mempty)
  where
    fixpointConstraint = toHornClause constraints
    cfg = C.defConfig { C.eliminate = C.Existentials } -- , C.save = True }
    measureHashMap measures = HM.fromList $ (\(name, typ) -> (fromString name, typeToSort typ)) <$> MAP.toList measures

-- TODO: HC.solve requires () but should take any type
toHornClause :: NNF HC.Pred -> HC.Cstr (String, SourceSpan)
toHornClause c = c'
  where c' = toHornClause' c

toHornClause' (Head loc r) = HC.Head r (pprint r, loc)
toHornClause' (CAnd cs) =
  HC.CAnd (fmap toHornClause' cs)
toHornClause' (All x typ r c) =
  HC.All (HC.Bind (fromString x) (typeToSort typ) r) (toHornClause' c)
toHornClause' (Any x typ r c) =
  HC.Any (HC.Bind (fromString x) (typeToSort typ) r) (toHornClause' c)

collectKVars :: (Located a) => HC.Cstr a -> [HC.Var (String, SourceSpan)]
collectKVars cstr = go MAP.empty cstr
  where
    go env (HC.Head pred _) = goPred env pred
    go env (HC.CAnd constraints) = concatMap (go env) constraints
    go env (HC.All bind constraint) = bindKVars ++ constraintKVars
      where
        env' = MAP.insert (HC.bSym bind) (HC.bSort bind) env
        bindKVars = goPred env' (HC.bPred bind)
        constraintKVars = go env' constraint
    go env (HC.Any bind constraint) = bindKVars ++ constraintKVars
      where
        env' = MAP.insert (HC.bSym bind) (HC.bSort bind) env
        bindKVars = goPred env' (HC.bPred bind)
        constraintKVars = go env' constraint

    goPred env var@(HC.Var k args) = [HC.HVar k argSorts ("", sourceSpan cstr)]
      where
        argSorts = map (\arg -> fromMaybe (error (show (arg, var))) $ MAP.lookup arg env) args
    goPred env (HC.PAnd preds) = concatMap (goPred env) preds
    goPred _ (HC.Reft _) = []

--------------------------------------------------------------------
-- | Translate base `Type`s to `Sort`s
--------------------------------------------------------------------
typeToSort :: M.Type -> F.Sort
typeToSort t = fromMaybe (error $ "typeToSort: " <> pprint t) $ safeTypeToSort t

safeTypeToSort :: M.Type -> Maybe F.Sort
safeTypeToSort (TVar (TV t)) = Just $ F.FVar (MN.varNum t) -- TODO: this is bad and needs to be changed
safeTypeToSort TUnit = Just $ F.FObj $ fromString "Unit"
safeTypeToSort TInt = Just F.intSort
safeTypeToSort TBool = Just F.boolSort
safeTypeToSort (TCtor "Set" [(_,t)]) = F.setSort <$> safeTypeToSort t
safeTypeToSort (TCtor "Map" [(_,t),(_,t')]) = F.mapSort <$> safeTypeToSort t <*> safeTypeToSort t'
-- is this backwards?
safeTypeToSort (t1 :=> t2) = F.FFunc <$> safeTypeToSort t1 <*> safeTypeToSort t2
-- We can't actually build arbitary TyCons in FP, so for now we just use
-- the constructor for Map for everything. Later we should make this work
-- with the liquid-fixpoint --adt setting, but I'm not sure how it iteracts
-- with FTyCon right now.
-- safeTypeToSort (TPair t1 t2) = F.FApp (F.FApp (F.FTC F.mapFTyCon) (safeTypeToSort t1)) (safeTypeToSort t2)
safeTypeToSort (TCtor (CT con) t2) = foldr F.FApp (F.FTC (F.symbolFTycon $ fromString con)) <$> (mapM (safeTypeToSort . snd) t2)
safeTypeToSort (TForall{}) = Nothing


--------------------------------------------------------------------
-- Expressions
--------------------------------------------------------------------
exprToFixpoint :: M.Expr t a -> Maybe F.Expr
exprToFixpoint (AnnNumber n _ _) = pure $ F.ECon (F.I n)
exprToFixpoint (AnnBoolean True _ _) = pure $ F.PTrue
exprToFixpoint (AnnBoolean False _ _) = pure $ F.PFalse
exprToFixpoint (AnnId x _ _) = pure $ idToFix x
exprToFixpoint (AnnPrim _ _ _) = error "primitives should be handled by appToFixpoint"
exprToFixpoint (AnnIf e1 e2 e3 _ _) =
  F.EIte <$> exprToFixpoint e1 <*> exprToFixpoint e2 <*> exprToFixpoint e3
exprToFixpoint e@AnnApp{} = appToFixpoint e
exprToFixpoint AnnLet{} = Nothing -- lets are currently unsupported inside refinements
exprToFixpoint (AnnUnit _ _) = pure $ F.EVar (fromString "()")
exprToFixpoint (AnnLam _bs _e2 _ _) = Nothing -- error "TODO exprToFixpoint"
exprToFixpoint (AnnTApp _e _typ _ _) = Nothing -- error "TODO exprToFixpoint"
exprToFixpoint (AnnTAbs _tvar _e _ _) = Nothing -- error "TODO exprToFixpoint"

appToFixpoint :: M.Expr t a -> Maybe F.Expr
appToFixpoint e
    | (AnnApp (AnnId n _ _ ) e1 _ _) <- e
    , "not" == MN.varHead n =
      F.PNot <$> exprToFixpoint e1
    | AnnApp (AnnApp (AnnPrim op _ _) e1 _ _) e2 _ _ <- e =
      binopToFixpoint op e1 e2
    | AnnApp (AnnApp (AnnTApp (AnnPrim op _ _) _ _ _) e1 _ _) e2 _ _ <- e =
      binopToFixpoint op e1 e2
    | AnnApp f x _ _ <- e =
      F.EApp <$> exprToFixpoint f <*> exprToFixpoint x
    | otherwise = error "non-application"

  where
    binopToFixpoint And e1 e2 = F.PAnd <$> sequence [exprToFixpoint e1, exprToFixpoint e2]
    binopToFixpoint Or e1 e2 = F.POr <$> sequence [exprToFixpoint e1, exprToFixpoint e2]
    binopToFixpoint Implies e1 e2 = F.PImp <$> exprToFixpoint e1 <*> exprToFixpoint e2
    binopToFixpoint op e1 e2 =
      case prim2ToFixpoint op of
        FBrel brel -> F.PAtom brel <$> exprToFixpoint e1 <*> exprToFixpoint e2
        FBop bop -> F.EBin bop <$> exprToFixpoint e1 <*> exprToFixpoint e2
        FPrim (F.EVar "internal_setDel") -> -- fixpoint's set_sng doesn't really work?
          F.EApp <$> (F.EApp (F.EVar T.setDif) <$> exprToFixpoint e1)
                 <*> (F.EApp (F.EApp (F.EVar T.setAdd) (F.EApp (F.EVar T.setEmpty) (F.ECon $ F.I 0))) <$> exprToFixpoint e2)
        FPrim e -> F.EApp <$> (F.EApp e <$> exprToFixpoint e1) <*> (exprToFixpoint e2)

data FPrim = FBop F.Bop | FBrel F.Brel | FPrim F.Expr

prim2ToFixpoint :: Prim -> FPrim
prim2ToFixpoint M.Plus  = FBop F.Plus
prim2ToFixpoint M.Minus = FBop F.Minus
prim2ToFixpoint M.Times = FBop F.Times
prim2ToFixpoint Less    = FBrel F.Lt
prim2ToFixpoint Lte     = FBrel F.Le
prim2ToFixpoint Greater = FBrel F.Gt
prim2ToFixpoint Equal   = FBrel F.Eq
prim2ToFixpoint NEqual  = FBrel F.Ne
prim2ToFixpoint Elem    = FPrim (F.EVar T.setMem)
prim2ToFixpoint SetAdd  = FPrim (F.EVar T.setAdd)
prim2ToFixpoint SetDel  = FPrim (F.EVar "internal_setDel")
prim2ToFixpoint SetSub  = FPrim (F.EVar T.setSub)
prim2ToFixpoint Store  = FPrim (F.EVar T.mapSto)
prim2ToFixpoint Select  = FPrim (F.EVar T.mapSel)
prim2ToFixpoint EmptySet  = FPrim (F.EVar T.setEmpty)
prim2ToFixpoint Union  = FPrim (F.EVar T.setCup)
prim2ToFixpoint Intersection  = FPrim (F.EVar T.setCap)
prim2ToFixpoint _       = error "Internal Error: prim2fp"

instance Predicate HC.Pred F.Expr where
  true = HC.Reft F.PTrue
  false = HC.Reft F.PFalse
  var x = F.EVar $ fromString x
  exprNot e = F.PNot $ e
  exprsEqual e1 e2 = F.PAtom F.Eq e1 e2
  interp e = exprToFixpoint e
  makePred e = HC.Reft e

  strengthen (HC.PAnd p1s) (HC.PAnd p2s) = HC.PAnd (p1s ++ p2s)
  strengthen (HC.PAnd p1s) p2 = HC.PAnd (p2:p1s)
  strengthen p1 (HC.PAnd p2s) = HC.PAnd (p1:p2s)
  strengthen p1 p2 = HC.PAnd [p1, p2]

  buildKvar x params = HC.Var (fromString x) (fmap fromString params)

  varSubstP su (HC.Reft fexpr) = HC.Reft $ F.subst fsu fexpr
    where
      fsu = F.Su $ HM.fromList $ bimap fromString (F.EVar . fromString) <$> MAP.toList su
  varSubstP su (HC.Var k params) =
    let su' = MAP.map fromString $ MAP.mapKeys fromString su in
    HC.Var k $ fmap (\param -> MAP.findWithDefault param param su') params
  varSubstP su (HC.PAnd ps) =
    HC.PAnd $ fmap (varSubstP su) ps

  substE su (HC.Reft fexpr) = HC.Reft $ F.subst fsu fexpr
    where
      fsu = F.Su $ HM.fromList $ first fromString <$> MAP.toList su
  substE _su _var@(HC.Var _ _params) =
    error "TODO: this doesn't work due to kvars"
    -- if null substitutedParams
    -- then var
    -- else HC.PAnd (var:equalities)
    -- where
    --   substitutedParams = params `intersect` (fromString <$> MAP.keys su)
    --   equalities = (\param -> makePred $ exprsEqual (F.EVar param) (su' MAP.! param)) <$> substitutedParams
    --   su' = MAP.mapKeys fromString su
  substE su (HC.PAnd ps) =
    HC.PAnd $ fmap (substE su) ps

  prim e@AnnUnit{} = equalityPrim e TUnit
  prim e@AnnNumber{} = equalityPrim e TInt
  prim e@AnnBoolean{} = equalityPrim e TBool
  prim (AnnPrim op _ l) = primOp op l
  prim _ = error "prim on non primitive"


equalityPrim :: (MonadFresh m, PPrint t) => M.Expr t a -> Type -> m (RType HC.Pred a)
equalityPrim e typ = do
  let l = extractLoc e
  vv <- refreshId $ "VV" ++ MN.cSEPARATOR
  let reft = HC.Reft $ F.PAtom F.Eq (idToFix vv) (fromMaybe (error $ "could not interperet " <> pprint e <> " as a fixpoint expression") (exprToFixpoint e))
  pure $ RBase (M.Bind vv l) typ reft

primOp :: (MonadFresh m) => Prim -> a -> m (RType HC.Pred a)
primOp op l =
  case op of
    Plus -> buildRFun (F.EBin F.Plus) TInt TInt
    Minus -> buildRFun (F.EBin F.Minus) TInt TInt
    Times -> buildRFun (F.EBin F.Times) TInt TInt
    Less -> buildRFun (F.PAtom F.Lt) TInt TBool
    Greater -> buildRFun (F.PAtom F.Gt) TInt TBool
    Lte -> buildRFun (F.PAtom F.Le) TInt TBool
    Equal -> do
      a <- refreshId $ "A" ++ MN.cSEPARATOR
      x <- refreshId $ "X" ++ MN.cSEPARATOR
      y <- refreshId $ "Y" ++ MN.cSEPARATOR
      v <- refreshId $ "EQ" ++ MN.cSEPARATOR
      v1 <- refreshId $ "VX" ++ MN.cSEPARATOR
      v2 <- refreshId $ "VY" ++ MN.cSEPARATOR
      let reft = HC.Reft $ F.PAtom F.Eq (idToFix v) $ F.PAtom F.Eq (idToFix x) (idToFix y)
      let returnType = RBase (Bind v l) TBool reft
      let typ1 = TVar $ TV a
      pure $ RForall (TV a) (RFun (Bind x l) (trivialBase typ1 v1) (RFun (Bind y l) (trivialBase typ1 v2) returnType))
    And -> buildRFun (\x y -> F.PAnd [x,y]) TBool TBool
    _ -> error $ "TODO: primOp " ++ show op

  where
    buildRFun oper typ1 typ2 = do
      x <- refreshId $ "X" ++ MN.cSEPARATOR
      y <- refreshId $ "Y" ++ MN.cSEPARATOR
      v <- refreshId $ "OP" ++ MN.cSEPARATOR
      v1 <- refreshId $ "VX" ++ MN.cSEPARATOR
      v2 <- refreshId $ "VY" ++ MN.cSEPARATOR
      let reft = HC.Reft $ F.PAtom F.Eq (idToFix v) (oper (idToFix x) (idToFix y))
      let returnType = RBase (Bind v l) typ2 reft
      pure $ RFun (Bind x l) (trivialBase typ1 v1) (RFun (Bind y l) (trivialBase typ1 v2) returnType)
    trivialBase typ x = RBase (Bind x l) typ true


-- | Converts a ParsedExpr's predicates from Exprs to Fixpoint Exprs
parsedExprPredToFixpoint :: ParsedExpr a -> RefinedExpr HC.Pred a
parsedExprPredToFixpoint = (first $ fmap (first (HC.Reft . (fromMaybe (error "failed to convert predicate")) . exprToFixpoint . unParsedExpr))) . unParsedExpr

idToFix :: Id -> F.Expr
idToFix x = F.EVar (fromString x)


------------------------------------------------------------------------------
-- PPrint
------------------------------------------------------------------------------

instance PPrint (HC.Pred) where
  pprint (HC.Reft expr) = printf "(%s)" (F.showpp expr)
  pprint (HC.Var kvar args) = printf "%s(%s)" (show kvar) (intercalate "," (fmap show args))
  pprint (HC.PAnd preds) = intercalate "/\\" (fmap pprint preds)
