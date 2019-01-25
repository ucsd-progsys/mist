{-# LANGUAGE StandaloneDeriving #-}
module Language.Mist.ToFixpoint
  (
    solve
  , insert
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
-- >>> let MC.CGInfo scs = MC.generateConstraints (CLet (AnnBind "y" rInt ()) (CUnit ()) (CApp (CLam (AnnBind "x" rInt ()) (CId "x" ()) ()) (CId "y" ()) ()) ())
-- >>> let hc = foldl insert (Head (HC.Reft F.PTrue) ()) scs
-- >>> S.solve defConfig (Query [] [] hc)
-- Result {resStatus = Safe, resSolution = fromList [], gresSolution = }

solve :: [MC.SubC a] -> IO (F.Result Integer)
solve scs = S.solve defConfig (Query [] [] hc)
  where hc = foldl insert (Head (HC.Reft F.PTrue) ()) (void <$> scs)

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
-- >>> let c = insert (Head (HC.Reft F.PTrue) ()) (MC.SubC [] (rt "v") (rt "v"))
-- >>> let c' = insert c (MC.SubC [("x", rt "x")] (rt "v") (rt "v"))
-- >>> let c'' = insert c'  (MC.SubC [("x", rt "x"),("y", rt "y")] (rt "v") (rt "v"))
-- >>> c''
-- CAnd [Head (Reft (PAnd [])) (),All (Bind {bSym = "v", bSort = FObj "Unit", bPred = Reft (PAtom Eq (EVar "v") (EVar "()"))}) (Head (Reft (PAtom Eq (EVar "v") (EVar "()"))) ()),All (Bind {bSym = "x", bSort = FObj "Unit", bPred = Reft (PAtom Eq (EVar "x") (EVar "()"))}) (CAnd [All (Bind {bSym = "v", bSort = FObj "Unit", bPred = Reft (PAtom Eq (EVar "v") (EVar "()"))}) (Head (Reft (PAtom Eq (EVar "v") (EVar "()"))) ()),All (Bind {bSym = "y", bSort = FObj "Unit", bPred = Reft (PAtom Eq (EVar "y") (EVar "()"))}) (All (Bind {bSym = "v", bSort = FObj "Unit", bPred = Reft (PAtom Eq (EVar "v") (EVar "()"))}) (Head (Reft (PAtom Eq (EVar "v") (EVar "()"))) ()))])]

insert :: Cstr a -> MC.SubC a -> Cstr a
insert
  c
  sc@(MC.SubC [] _ _)
  = addNode c sc

insert
  c'@(HC.All b@(HC.Bind x _ _) c)
  sc@(MC.SubC ((x',_):xs) l r)
  = if x == fromString x'
      then HC.All b (insert c (MC.SubC xs l r))
      else addNode c' sc

insert
  (HC.CAnd cs)
  sc@(MC.SubC ((x',_):_) _ _)
  = CAnd $ insertOne (fromString x') sc cs

insert
  c@HC.Head{}
  sc
  = addNode c sc

insertOne :: F.Symbol -> MC.SubC a -> [Cstr a] -> [Cstr a]
insertOne x sc (c@(HC.All (HC.Bind x' _ _) _):cs) =
    if x == x' then insert c sc : cs
               else c : insertOne x sc cs
insertOne x sc (c@Head{}:cs) =  c : insertOne x sc cs
-- CAnd should never be followed by another CAnd
insertOne _x _sc (_c@CAnd{}:_cs) = error "CAnd followed by CAnd" -- c : insertOne x sc cs
insertOne _ sc [] = [subCtoHC sc]

addNode :: Cstr a -> MC.SubC a -> Cstr a
addNode (HC.CAnd xs) sc = HC.CAnd $ subCtoHC sc : xs
addNode c sc = HC.CAnd [c, subCtoHC sc]

subCtoHC (MC.SubC [] l r) = HC.All (HC.Bind (fromString lid) (typeToSort lsort) lpred) hd
    where -- vv = refreshId "VV##" lid
          (lid, lsort, lreft, tag)  = bkRType l
          (_rid, _rsort, rreft, _) = bkRType r -- TODO: assert that r has the same sort?
          lpred = HC.Reft $ coreToFixpoint $ lreft -- subst1 lid vv lreft
          rpred = HC.Reft $ coreToFixpoint $ rreft -- subst1 rid vv rreft
          hd = Head rpred tag
subCtoHC (MC.SubC ((x,rt):bs) l r) = HC.All (HC.Bind (fromString x) sort pred) (subCtoHC (MC.SubC bs l r))
      where sort = typeToSort $ eraseRType rt
            pred = HC.Reft $ coreToFixpoint reft
            reft = reftRType rt

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
