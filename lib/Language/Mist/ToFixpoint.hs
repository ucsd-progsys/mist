module Language.Mist.ToFixpoint ( exprToFixpoint, coreToFixpoint ) where

import Data.String (fromString)

import Language.Mist.Types     as M
import Language.Mist.Fresh (varNum)
import Language.Fixpoint.Types as F

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
coreToFixpoint (CGetItem e Zero _) =
  EApp (EVar $ fromString "Pi0") (coreToFixpoint e)
coreToFixpoint (CGetItem e One _)  =
  EApp (EVar $ fromString "Pi1") (coreToFixpoint e)
coreToFixpoint (CLam _bs _e2 _)    = error "TODO coreToFixpoint"
coreToFixpoint (CTApp e tau _)     = ETApp (coreToFixpoint e) (typeToSort tau)
coreToFixpoint (CTAbs _as e _)      = ETAbs (coreToFixpoint e) (error "TODO coreToFixpoint TVar")

typeToSort :: M.Type -> F.Sort
typeToSort (TVar (TV t)) = FVar (varNum t)
typeToSort TInt = FInt
typeToSort TBool = undefined
-- is this backwards?
typeToSort (t1 :=> t2) = foldr FFunc (typeToSort t2) (typeToSort <$> t1)
-- We can't actually build arbitary TyCons in FP, so for now we just use
-- the constructor for Map for everything. Later we should make this work
-- with the liquid-fixpoint --adt setting, but I'm not sure how it iteracts
-- with FTyCon right now.
typeToSort (TPair t1 t2) = FApp (FApp (FTC mapFTyCon) (typeToSort t1)) (typeToSort t2)
typeToSort (TCtor _ t2) = foldr FApp (FTC mapFTyCon) (typeToSort <$> t2)

prim2ToFixpoint :: Prim2 -> Either Brel Bop
prim2ToFixpoint M.Plus  = Right F.Plus
prim2ToFixpoint M.Minus = Right F.Minus
prim2ToFixpoint M.Times = Right F.Times
prim2ToFixpoint Less    = Left Lt
prim2ToFixpoint Greater = Left Gt
prim2ToFixpoint Equal   = Left Eq
