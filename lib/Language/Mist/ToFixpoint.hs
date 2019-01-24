{-# LANGUAGE StandaloneDeriving #-}
module Language.Mist.ToFixpoint
  (
    exprToFixpoint
  , coreToFixpoint
  , insert
  ) where

import Data.String (fromString)

import Language.Mist.Types     as M
import Language.Mist.CGen      as MC
import Language.Mist.Names

import Language.Fixpoint.Types      as F
import Language.Fixpoint.Horn.Types as HC

--------------------------------------------------------------------
-- NNF Horn Clauses as tries of subCs
--------------------------------------------------------------------
-- We can build one out of a bunch of SubCs. SubCs here should only
-- contain RRTy and RBase

deriving instance Show HC.Pred
deriving instance Show HC.Bind
deriving instance Show a => Show (Cstr a)

-- |
-- >>> let rt x  = RBase (M.Bind {bindId = x, bindLabel = ()}) TUnit (CPrim2 Equal (CId x  ()) (CUnit ()) ())
-- >>> let c = insert (Head (HC.Reft F.PTrue) ()) (SubC [] (rt "v") (rt "v"))
-- >>> let c' = insert c (SubC [("x", rt "x")] (rt "v") (rt "v"))
-- >>> let c'' = insert c'  (SubC [("x", rt "x"),("y", rt "y")] (rt "v") (rt "v"))
-- >>> c''
-- CAnd [Head (Reft (PAnd [])) (),All (Bind {bSym = "v", bSort = FObj "Unit", bPred = Reft (PAtom Eq (EVar "v") (EVar "()"))}) (Head (Reft (PAtom Eq (EVar "v") (EVar "()"))) ()),All (Bind {bSym = "x", bSort = FObj "Unit", bPred = Reft (PAtom Eq (EVar "x") (EVar "()"))}) (CAnd [All (Bind {bSym = "v", bSort = FObj "Unit", bPred = Reft (PAtom Eq (EVar "v") (EVar "()"))}) (Head (Reft (PAtom Eq (EVar "v") (EVar "()"))) ()),All (Bind {bSym = "y", bSort = FObj "Unit", bPred = Reft (PAtom Eq (EVar "y") (EVar "()"))}) (All (Bind {bSym = "v", bSort = FObj "Unit", bPred = Reft (PAtom Eq (EVar "v") (EVar "()"))}) (Head (Reft (PAtom Eq (EVar "v") (EVar "()"))) ()))])]

insert :: HC.Cstr a -> MC.SubC a -> HC.Cstr a
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

insertOne :: Symbol -> MC.SubC a -> [Cstr a] -> [Cstr a]
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

subCtoHC (SubC [] l r) = HC.All (HC.Bind (fromString lid) (typeToSort lsort) lpred) hd
    where -- vv = refreshId "VV##" lid
          (lid, lsort, lreft, tag)  = bkRType l
          (_rid, _rsort, rreft, _) = bkRType r -- TODO: assert that r has the same sort?
          lpred = HC.Reft $ coreToFixpoint $ lreft -- subst1 lid vv lreft
          rpred = HC.Reft $ coreToFixpoint $ rreft -- subst1 rid vv rreft
          hd = Head rpred tag
subCtoHC (SubC ((x,rt):bs) l r) = HC.All (HC.Bind (fromString x) sort pred) (subCtoHC (SubC bs l r))
      where sort = typeToSort $ eraseRType rt
            pred = HC.Reft $ coreToFixpoint reft
            reft = reftRType rt

--------------------------------------------------------------------
-- | Translate base `Type`s to `Sort`s
--------------------------------------------------------------------
typeToSort :: M.Type -> F.Sort
typeToSort (TVar (TV t)) = FVar (varNum t)
typeToSort TUnit = FObj $ fromString "Unit"
typeToSort TInt = FInt
typeToSort TBool = undefined
-- is this backwards?
typeToSort (t1 :=> t2) = FFunc (typeToSort t1) (typeToSort t2)
-- We can't actually build arbitary TyCons in FP, so for now we just use
-- the constructor for Map for everything. Later we should make this work
-- with the liquid-fixpoint --adt setting, but I'm not sure how it iteracts
-- with FTyCon right now.
typeToSort (TPair t1 t2) = FApp (FApp (FTC mapFTyCon) (typeToSort t1)) (typeToSort t2)
typeToSort (TCtor _ t2) = foldr FApp (FTC mapFTyCon) (typeToSort <$> t2)
typeToSort (TForall{}) = error "TODO?"


--------------------------------------------------------------------
-- Expressions
--------------------------------------------------------------------
exprToFixpoint :: M.Expr a -> F.Expr
exprToFixpoint (Number n _)       = ECon (I n)
exprToFixpoint (Boolean True _)   = PTrue
exprToFixpoint (Boolean False _)  = PFalse
exprToFixpoint (Id x _)           = EVar (fromString x)
exprToFixpoint (Prim2 o e1 e2 _)  =
  case prim2ToFixpoint o of
    Left brel -> PAtom brel (exprToFixpoint e1) (exprToFixpoint e2)
    Right bop -> EBin bop (exprToFixpoint e1) (exprToFixpoint e2)
exprToFixpoint (If e1 e2 e3 _)    =
  EIte (exprToFixpoint e1) (exprToFixpoint e2) (exprToFixpoint e3)
exprToFixpoint (App f x _)        =
  EApp (exprToFixpoint f) (exprToFixpoint x)
exprToFixpoint Let{}              =
  error "lets are currently unsupported inside reifnements"
exprToFixpoint (Unit _)           = EVar (fromString "()")
exprToFixpoint (Tuple e1 e2 _)    =
  EApp (EApp (EVar $ fromString "(,)")
             (exprToFixpoint e1))
       (exprToFixpoint e2)
exprToFixpoint (GetItem e Zero _) =
  EApp (EVar $ fromString "Pi0") (exprToFixpoint e)
exprToFixpoint (GetItem e One _)  =
  EApp (EVar $ fromString "Pi1") (exprToFixpoint e)
  -- To translate Lambdas we need to keep around the sorts of each Expr. We
  -- can do this in Core, but doing it in Expr seems like it's not work it.
exprToFixpoint (Lam _bs _e2 _)      = error "TODO exprToFixpoint"

coreToFixpoint :: Core a -> F.Expr
coreToFixpoint (CNumber n _)       = ECon (I n)
coreToFixpoint (CBoolean True _)   = PTrue
coreToFixpoint (CBoolean False _)  = PFalse
coreToFixpoint (CId x _)           = EVar (fromString x)
coreToFixpoint (CPrim2 And e1 e2 _)= F.PAnd [coreToFixpoint e1, coreToFixpoint e2]
coreToFixpoint (CPrim2 o e1 e2 _)  =
  case prim2ToFixpoint o of
    Left brel -> PAtom brel (coreToFixpoint e1) (coreToFixpoint e2)
    Right bop -> EBin bop (coreToFixpoint e1) (coreToFixpoint e2)
coreToFixpoint (CIf e1 e2 e3 _)    =
  EIte (coreToFixpoint e1) (coreToFixpoint e2) (coreToFixpoint e3)
coreToFixpoint (CApp f x _)        =
  EApp (coreToFixpoint f) (coreToFixpoint x)
coreToFixpoint CLet{}              =
  error "lets are currently unsupported inside reifnements"
coreToFixpoint (CUnit _)           = EVar (fromString "()")
coreToFixpoint (CTuple e1 e2 _)    =
  EApp (EApp (EVar $ fromString "(,)")
             (coreToFixpoint e1))
       (coreToFixpoint e2)
coreToFixpoint (CPrim prim _)      = primToFixpoint prim
coreToFixpoint (CLam _bs _e2 _)    = error "TODO coreToFixpoint"
coreToFixpoint (CTApp e tau _)     = ETApp (coreToFixpoint e) (typeToSort tau)
coreToFixpoint (CTAbs _as e _)     = ETAbs (coreToFixpoint e) (error "TODO coreToFixpoint TVar")

primToFixpoint :: Prim -> F.Expr
primToFixpoint Pi0 = EVar $ fromString "Pi0"
primToFixpoint Pi1 = EVar $ fromString "Pi1"

prim2ToFixpoint :: Prim2 -> Either F.Brel F.Bop
prim2ToFixpoint M.Plus  = Right F.Plus
prim2ToFixpoint M.Minus = Right F.Minus
prim2ToFixpoint M.Times = Right F.Times
prim2ToFixpoint Less    = Left Lt
prim2ToFixpoint Greater = Left Gt
prim2ToFixpoint Equal   = Left Eq
prim2ToFixpoint _       = error "Internal Error: prim2fp"
