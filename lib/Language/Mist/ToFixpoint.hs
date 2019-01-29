{-# LANGUAGE StandaloneDeriving #-}
module Language.Mist.ToFixpoint
  (
    solve
  ) where

import Data.String (fromString)
import Control.Monad (void)

import           Language.Mist.Types     as M
import qualified Language.Mist.CGen      as MC
import qualified Language.Mist.Names     as MN

import           Language.Fixpoint.Types.Config (defConfig)
import qualified Language.Fixpoint.Types      as F
import           Language.Fixpoint.Horn.Types as HC
import qualified Language.Fixpoint.Horn.Solve as S

-- | Solves the subtyping constraints we got from CGen.

-- |
-- >>> let rInt = RBase (M.Bind "VV" ()) TInt (CBoolean True ())
-- >>> let cs = MC.generateConstraints (CApp (CLam (AnnBind "x" rInt ()) (CId "x" ()) ()) (CNumber 2 ()) ())
-- >>> solve cs
-- Result {resStatus = Safe, resSolution = fromList [], gresSolution = }

-- TODO:
-- >>> let cs = MC.generateConstraints (CLet (AnnBind "y" rInt ()) (CUnit ()) (CApp (CLam (AnnBind "x" rInt ()) (CId "x" ()) ()) (CId "y" ()) ()) ())
-- >>> solve cs
-- Result {resStatus = Safe, resSolution = fromList [], gresSolution = }

solve :: MC.SubC a -> IO (F.Result Integer)
solve sc = S.solve defConfig (Query [] [] hc)
  where hc = void $ toHC sc

--------------------------------------------------------------------
-- NNF Horn Clauses as tries of subCs
--------------------------------------------------------------------
-- We can build one out of a bunch of SubCs. SubCs here should only
-- contain RRTy and RBase

deriving instance Show HC.Pred
deriving instance Show HC.Bind
deriving instance Show a => Show (Cstr a)

-- | Adds a subtyping constraint to an exsiting NNF HC

-- |
-- >>> let rt x  = RBase (M.Bind {bindId = x, bindLabel = ()}) TUnit (CPrim2 Equal (CId x  ()) (CUnit ()) ())
-- >>>  let h = MC.SHead $ CPrim2 Equal (CId "v" ()) (CId "v"()) ()
-- >>>  let c = MC.SAll "x" (rt "x") $ MC.SAnd (MC.SAll "y" (rt "y") (MC.SAll "v" (rt "v") h)) (MC.SAll "v" (rt "v") h)
-- >>> toHC c
-- All (Bind {bSym = "x", bSort = FObj "Unit", bPred = Reft (PAtom Eq (EVar "x") (EVar "()"))}) (CAnd [All (Bind {bSym = "y", bSort = FObj "Unit", bPred = Reft (PAtom Eq (EVar "y") (EVar "()"))}) (All (Bind {bSym = "v", bSort = FObj "Unit", bPred = Reft (PAtom Eq (EVar "v") (EVar "()"))}) (Head (Reft (PAtom Eq (EVar "v") (EVar "v"))) ())),All (Bind {bSym = "v", bSort = FObj "Unit", bPred = Reft (PAtom Eq (EVar "v") (EVar "()"))}) (Head (Reft (PAtom Eq (EVar "v") (EVar "v"))) ())])

toHC (MC.SAll x rt c) = HC.All (HC.Bind (fromString x) (typeToSort tau) (Reft $ coreToFixpoint $ MN.subst1 (CId x l) y p)) (toHC c)
  where (y, tau, p, l) = bkRType rt
toHC (MC.SHead e) = HC.Head (HC.Reft $ coreToFixpoint e) (extractC e)
toHC c@MC.SAnd{} = HC.CAnd $ toHC <$> bkSAnd c

bkSAnd (MC.SAnd c1 c2) = bkSAnd c1 ++ bkSAnd c2
bkSAnd c@MC.SAll{} = pure c
bkSAnd c@MC.SHead{} = pure c

--------------------------------------------------------------------
-- | Translate base `Type`s to `Sort`s
--------------------------------------------------------------------
typeToSort :: M.Type -> F.Sort
typeToSort (TVar (TV t)) = F.FVar (MN.varNum t)
typeToSort TUnit = F.FObj $ fromString "Unit"
typeToSort TInt = F.FInt
typeToSort TBool = undefined
-- is this backwards?
typeToSort (t1 :=> t2) = F.FFunc (typeToSort t1) (typeToSort t2)
-- We can't actually build arbitary TyCons in FP, so for now we just use
-- the constructor for Map for everything. Later we should make this work
-- with the liquid-fixpoint --adt setting, but I'm not sure how it iteracts
-- with FTyCon right now.
typeToSort (TPair t1 t2) = F.FApp (F.FApp (F.FTC F.mapFTyCon) (typeToSort t1)) (typeToSort t2)
typeToSort (TCtor _ t2) = foldr F.FApp (F.FTC F.mapFTyCon) (typeToSort <$> t2)
typeToSort (TForall{}) = error "TODO?"


--------------------------------------------------------------------
-- Expressions
--------------------------------------------------------------------
_exprToFixpoint = exprToFixpoint
exprToFixpoint :: M.Expr a -> F.Expr
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
exprToFixpoint (Tuple e1 e2 _)    =
  F.EApp (F.EApp (F.EVar $ fromString "(,)")
                 (exprToFixpoint e1))
       (exprToFixpoint e2)
exprToFixpoint (GetItem e Zero _) =
  F.EApp (F.EVar $ fromString "Pi0") (exprToFixpoint e)
exprToFixpoint (GetItem e One _)  =
  F.EApp (F.EVar $ fromString "Pi1") (exprToFixpoint e)
  -- To translate Lambdas we need to keep around the sorts of each Expr. We
  -- can do this in Core, but doing it in Expr seems like it's not work it.
exprToFixpoint (Lam _bs _e2 _)      = error "TODO exprToFixpoint"

coreToFixpoint :: Core a -> F.Expr
coreToFixpoint (CNumber n _)       = F.ECon (F.I n)
coreToFixpoint (CBoolean True _)   = F.PTrue
coreToFixpoint (CBoolean False _)  = F.PFalse
coreToFixpoint (CId x _)           = F.EVar (fromString x)
coreToFixpoint (CPrim2 And e1 e2 _)= F.PAnd [coreToFixpoint e1, coreToFixpoint e2]
coreToFixpoint (CPrim2 o e1 e2 _)  =
  case prim2ToFixpoint o of
    Left brel -> F.PAtom brel (coreToFixpoint e1) (coreToFixpoint e2)
    Right bop -> F.EBin bop (coreToFixpoint e1) (coreToFixpoint e2)
coreToFixpoint (CIf e1 e2 e3 _)    =
  F.EIte (coreToFixpoint e1) (coreToFixpoint e2) (coreToFixpoint e3)
coreToFixpoint (CApp f x _)        =
  F.EApp (coreToFixpoint f) (coreToFixpoint x)
coreToFixpoint CLet{}              =
  error "lets are currently unsupported inside reifnements"
coreToFixpoint (CUnit _)           = F.EVar (fromString "()")
coreToFixpoint (CTuple e1 e2 _)    =
  F.EApp (F.EApp (F.EVar $ fromString "(,)")
               (coreToFixpoint e1))
       (coreToFixpoint e2)
coreToFixpoint (CPrim prim _)      = primToFixpoint prim
coreToFixpoint (CLam _bs _e2 _)    = error "TODO coreToFixpoint"
coreToFixpoint (CTApp e tau _)     = F.ETApp (coreToFixpoint e) (typeToSort tau)
coreToFixpoint (CTAbs _as e _)     = F.ETAbs (coreToFixpoint e) (error "TODO coreToFixpoint TVar")

primToFixpoint :: Prim -> F.Expr
primToFixpoint Pi0 = F.EVar $ fromString "Pi0"
primToFixpoint Pi1 = F.EVar $ fromString "Pi1"

prim2ToFixpoint :: Prim2 -> Either F.Brel F.Bop
prim2ToFixpoint M.Plus  = Right F.Plus
prim2ToFixpoint M.Minus = Right F.Minus
prim2ToFixpoint M.Times = Right F.Times
prim2ToFixpoint Less    = Left F.Lt
prim2ToFixpoint Greater = Left F.Gt
prim2ToFixpoint Equal   = Left F.Eq
prim2ToFixpoint _       = error "Internal Error: prim2fp"
