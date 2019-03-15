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
import Data.List (intercalate)
import Text.Printf

import Language.Mist.Types as M
import qualified Language.Mist.Names as MN

import qualified Language.Fixpoint.Types.Config as C
import qualified Language.Fixpoint.Types as F
import qualified Language.Fixpoint.Horn.Types as HC
import qualified Language.Fixpoint.Horn.Solve as S
import System.Console.CmdArgs.Verbosity

-- | Solves the subtyping constraints we got from CGen.

solve :: M.Constraint HC.Pred -> IO (F.Result Integer)
solve constraints = {-setVerbosity Loud >>-} S.solve cfg (HC.Query [] (collectKVars fixpointConstraint) fixpointConstraint mempty mempty)
  where
    fixpointConstraint = toHornClause constraints
    cfg = C.defConfig { C.eliminate = C.Existentials } -- , C.save = True }

-- TODO: HC.solve requires () but should take any type
toHornClause :: Constraint HC.Pred -> HC.Cstr ()
toHornClause c = c'
  where c' = toHornClause' c

toHornClause' (Head r) = HC.Head r ()
toHornClause' (CAnd cs) =
  HC.CAnd (fmap toHornClause' cs)
toHornClause' (All x typ r c) =
  HC.All (HC.Bind (fromString x) (typeToSort typ) r) (toHornClause' c)
toHornClause' (Any x typ r c) =
  HC.Any (HC.Bind (fromString x) (typeToSort typ) r) (toHornClause' c)

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
    go env (HC.Any bind constraint) = bindKVars ++ constraintKVars
      where
        env' = MAP.insert (HC.bSym bind) (HC.bSort bind) env
        bindKVars = goPred env' (HC.bPred bind)
        constraintKVars = go env' constraint

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
typeToSort TBool = F.boolSort
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
exprToFixpoint (Prim _ _)         = error "primitives should be handled by appToFixpoing"
exprToFixpoint (If e1 e2 e3 _)    =
  F.EIte (exprToFixpoint e1) (exprToFixpoint e2) (exprToFixpoint e3)
exprToFixpoint e@App{}            =
  appToFixpoint e
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

    -- case prim2ToFixpoint o of
    -- Left brel -> F.PAtom brel (exprToFixpoint e1) (exprToFixpoint e2)
    -- Right bop -> F.EBin bop (exprToFixpoint e1) (exprToFixpoint e2)

appToFixpoint :: M.Expr r a -> F.Expr
appToFixpoint e =
  case e of
    App (App (Prim op _) e1 _) e2 _ ->
      binopToFixpoint op e1 e2
    App (App (TApp (Prim op _) _ _) e1 _) e2 _ ->
      binopToFixpoint op e1 e2
    App f x _ ->
      F.EApp (exprToFixpoint f) (exprToFixpoint x)
    _ -> error "non-application"

  where
    binopToFixpoint op e1 e2 =
      case prim2ToFixpoint op of
        Left brel -> F.PAtom brel (exprToFixpoint e1) (exprToFixpoint e2)
        Right bop -> F.EBin bop (exprToFixpoint e1) (exprToFixpoint e2)

prim2ToFixpoint :: Prim -> Either F.Brel F.Bop
prim2ToFixpoint M.Plus  = Right F.Plus
prim2ToFixpoint M.Minus = Right F.Minus
prim2ToFixpoint M.Times = Right F.Times
prim2ToFixpoint Less    = Left F.Lt
prim2ToFixpoint Lte     = Left F.Le
prim2ToFixpoint Greater = Left F.Gt
prim2ToFixpoint Equal   = Left F.Eq
prim2ToFixpoint _       = error "Internal Error: prim2fp"

instance Predicate HC.Pred where
  true = HC.Reft F.PTrue
  false = HC.Reft F.PFalse
  var x = HC.Reft $ F.EVar $ fromString x
  varNot x  = HC.Reft $ F.PNot $ F.EVar $ fromString x
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
  prim (Prim op l) = primOp op l
  prim _ = error "prim on non primitive"

equalityPrim :: (MonadFresh m) => Expr r a -> Type -> m (RType HC.Pred a)
equalityPrim e typ = do
  let l = extract e
  vv <- refreshId $ "VV" ++ MN.cSEPARATOR
  let reft = HC.Reft $ F.PAtom F.Eq (exprToFixpoint (Id vv l)) (exprToFixpoint e)
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
      v <- refreshId $ "VV" ++ MN.cSEPARATOR
      v1 <- refreshId $ "VV" ++ MN.cSEPARATOR
      v2 <- refreshId $ "VV" ++ MN.cSEPARATOR
      let reft = HC.Reft $ F.PAtom F.Eq (idToFix x) (idToFix y)
      let returnType = RBase (Bind v l) TBool reft
      let typ1 = TVar $ TV a
      pure $ RForall (TV a) (RFun (Bind x l) (trivialBase typ1 v1) (RFun (Bind y l) (trivialBase typ1 v2) returnType))
    And -> error "TODO"

  where
    buildRFun oper typ1 typ2 = do
      x <- refreshId $ "X" ++ MN.cSEPARATOR
      y <- refreshId $ "Y" ++ MN.cSEPARATOR
      v <- refreshId $ "VV" ++ MN.cSEPARATOR
      v1 <- refreshId $ "VV" ++ MN.cSEPARATOR
      v2 <- refreshId $ "VV" ++ MN.cSEPARATOR
      let reft = HC.Reft $ F.PAtom F.Eq (idToFix v) (oper (idToFix x) (idToFix y))
      let returnType = RBase (Bind v l) typ2 reft
      pure $ RFun (Bind x l) (trivialBase typ1 v1) (RFun (Bind y l) (trivialBase typ1 v2) returnType)
    idToFix x = exprToFixpoint (Id x l)
    trivialBase typ x = RBase (Bind x l) typ true


-- | Converts a ParsedExpr's predicates from Exprs to Fixpoint Exprs
parsedExprPredToFixpoint :: ParsedExpr (Expr r a) a -> ParsedExpr HC.Pred a
parsedExprPredToFixpoint = first $ first (HC.Reft . exprToFixpoint)


------------------------------------------------------------------------------
-- PPrint
------------------------------------------------------------------------------

instance PPrint (HC.Pred) where
  pprint (HC.Reft expr) = printf "(%s)" (show expr)
  pprint (HC.Var kvar args) = printf "%s(%s)" (show kvar) (intercalate "," (fmap show args))
  pprint (HC.PAnd preds) = intercalate "/\\" (fmap pprint preds)
