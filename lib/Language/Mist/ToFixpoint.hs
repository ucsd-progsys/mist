{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DeriveFunctor #-}

module Language.Mist.ToFixpoint
  ( solve
  , exprToFixpoint
  , parsedExprPredToFixpoint
  ) where

import Data.String (fromString)
import Data.Bifunctor
import qualified Data.Map.Strict as MAP
import Data.Maybe (fromMaybe)

import Language.Mist.Types as M
import Language.Mist.Checker (primToUnpoly) -- TODO(Matt): move primToUnpoly to a better place
import qualified Language.Mist.Names as MN

import qualified Language.Fixpoint.Types.Config as C
import qualified Language.Fixpoint.Types as F
import qualified Language.Fixpoint.Horn.Types as HC
import qualified Language.Fixpoint.Horn.Solve as S

-- | Solves the subtyping constraints we got from CGen.

solve :: M.Constraint HC.Pred -> IO (F.Result Integer)
solve constraints = S.solve cfg (HC.Query [] (collectKVars fixpointConstraint) fixpointConstraint)
  where
    fixpointConstraint = toHornClause constraints
    cfg = C.defConfig { C.eliminate = C.Some , C.save = True }

-- TODO: HC.solve requires () but should take any type
toHornClause :: Constraint HC.Pred -> HC.Cstr ()
toHornClause (Head r) = HC.Head r ()
toHornClause (CAnd cs) =
  HC.CAnd (fmap toHornClause cs)
toHornClause (All x typ r c) =
  HC.All (HC.Bind (fromString x) (typeToSort typ) r) (toHornClause c)

collectKVars :: HC.Cstr a -> [HC.Var ()]
collectKVars cstr = go MAP.empty cstr
  where
    go env (HC.Head pred _) = goPred env pred
    go env (HC.CAnd constraints) = concatMap (go env) constraints
    go env (HC.All bind constraint) = bindKVars ++ constraintKVars
      where
        env' = MAP.insert (HC.bSym bind) (HC.bSort bind) env
        bindKVars = goPred env' (HC.bPred bind)
        constraintKVars = go env' constraint
    go _ (HC.Any{}) = undefined

    goPred env (HC.Var k args) = [HC.HVar k argSorts ()]
      where
        argSorts = map (\arg -> fromMaybe (error (show arg)) $ MAP.lookup arg env) args
    goPred env (HC.PAnd preds) = concatMap (goPred env) preds
    goPred _ (HC.Reft _) = []

--------------------------------------------------------------------
-- | Translate base `Type`s to `Sort`s
--------------------------------------------------------------------
typeToSort :: M.Type -> F.Sort
typeToSort (TVar (TV t)) = F.FVar (MN.varNum t) -- TODO: this is bad and needs to be changed
typeToSort TUnit = F.FObj $ fromString "Unit"
typeToSort TInt = F.FInt
typeToSort TBool = undefined
-- is this backwards?
typeToSort (t1 :=> t2) = F.FFunc (typeToSort t1) (typeToSort t2)
-- We can't actually build arbitary TyCons in FP, so for now we just use
-- the constructor for Map for everything. Later we should make this work
-- with the liquid-fixpoint --adt setting, but I'm not sure how it iteracts
-- with FTyCon right now.
-- typeToSort (TPair t1 t2) = F.FApp (F.FApp (F.FTC F.mapFTyCon) (typeToSort t1)) (typeToSort t2)
typeToSort (TCtor _ t2) = foldr F.FApp (F.FTC F.mapFTyCon) (typeToSort <$> t2)
typeToSort (TForall{}) = error "TODO?"


--------------------------------------------------------------------
-- Expressions
--------------------------------------------------------------------
exprToFixpoint :: M.Expr r a -> F.Expr
exprToFixpoint (Number n _)       = F.ECon (F.I n)
exprToFixpoint (Boolean True _)   = F.PTrue
exprToFixpoint (Boolean False _)  = F.PFalse
exprToFixpoint (Id x _)           = F.EVar (fromString x)
exprToFixpoint (Prim2 o e1 e2 _)  =
  case prim2ToFixpoint o of
    Left brel -> F.PAtom brel (exprToFixpoint e1) (exprToFixpoint e2)
    Right bop -> F.EBin bop (exprToFixpoint e1) (exprToFixpoint e2)
exprToFixpoint (If e1 e2 e3 _)    =
  F.EIte (exprToFixpoint e1) (exprToFixpoint e2) (exprToFixpoint e3)
exprToFixpoint (App f x _)        =
  F.EApp (exprToFixpoint f) (exprToFixpoint x)
exprToFixpoint Let{}              =
  error "lets are currently unsupported inside reifnements"
exprToFixpoint (Unit _)           = F.EVar (fromString "()")
-- exprToFixpoint (Tuple e1 e2 _)    =
--   F.EApp (F.EApp (F.EVar $ fromString "(,)")
--                  (exprToFixpoint e1))
--        (exprToFixpoint e2)
-- exprToFixpoint (GetItem e Zero _) =
--   F.EApp (F.EVar $ fromString "Pi0") (exprToFixpoint e)
-- exprToFixpoint (GetItem e One _)  =
--   F.EApp (F.EVar $ fromString "Pi1") (exprToFixpoint e)
--   -- To translate Lambdas we need to keep around the sorts of each Expr. We
--   -- can do this in Core, but doing it in Expr seems like it's not work it.
exprToFixpoint (Lam _bs _e2 _)      = error "TODO exprToFixpoint"
exprToFixpoint (TApp _e _typ _)      = error "TODO exprToFixpoint"
exprToFixpoint (TAbs _tvar _e _)      = error "TODO exprToFixpoint"

prim2ToFixpoint :: Prim2 -> Either F.Brel F.Bop
prim2ToFixpoint M.Plus  = Right F.Plus
prim2ToFixpoint M.Minus = Right F.Minus
prim2ToFixpoint M.Times = Right F.Times
prim2ToFixpoint Less    = Left F.Lt
prim2ToFixpoint Greater = Left F.Gt
prim2ToFixpoint Equal   = Left F.Eq
prim2ToFixpoint _       = error "Internal Error: prim2fp"

instance Predicate HC.Pred where
  true = HC.Reft F.PTrue
  false = HC.Reft F.PFalse
  varsEqual x y = HC.Reft $ F.PAtom F.Eq (F.EVar $ fromString x) (F.EVar $ fromString y)

  strengthen (HC.PAnd p1s) (HC.PAnd p2s) = HC.PAnd (p1s ++ p2s)
  strengthen (HC.PAnd p1s) p2 = HC.PAnd (p2:p1s)
  strengthen p1 (HC.PAnd p2s) = HC.PAnd (p1:p2s)
  strengthen p1 p2 = HC.PAnd [p1, p2]

  buildKvar x params = HC.Var (fromString x) (fmap fromString params)

  varSubst x y (HC.Reft fexpr) =
    HC.Reft $ F.subst1 fexpr (fromString y, F.EVar $ fromString x)
  varSubst x y (HC.Var k params) =
    HC.Var k $ fmap (\param -> if param == fromString y then fromString x else param) params
  varSubst x y (HC.PAnd ps) =
    HC.PAnd $ fmap (varSubst x y) ps

  prim e@Unit{} = equalityPrim e TUnit
  prim e@Number{} = equalityPrim e TInt
  prim e@Boolean{} = equalityPrim e TBool
  prim e@(Prim2 op _ _ _) = equalityPrim e (primToUnpoly op)
  prim _ = error "prim on non primitive"

equalityPrim :: (MonadFresh m) => Expr r a -> Type -> m (RType HC.Pred a)
equalityPrim e typ = do
  let l = extract e
  vv <- refreshId $ "VV" ++ MN.cSEPARATOR
  let reft = HC.Reft $ F.PAtom F.Eq (exprToFixpoint (Id vv l)) (exprToFixpoint e)
  pure $ RBase (M.Bind vv l) typ reft

-- | Converts a ParsedExpr's predicates from Exprs to Fixpoint Exprs
parsedExprPredToFixpoint :: ParsedExpr (Expr r a) a -> ParsedExpr HC.Pred a
parsedExprPredToFixpoint = first $ first (HC.Reft . exprToFixpoint)
