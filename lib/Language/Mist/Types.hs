{-# LANGUAGE DeriveFunctor        #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}

module Language.Mist.Types
  (
  -- * Re-Export SourceSpans
    module Language.Mist.UX

  -- * Aliases for various identifiers
  , Id

  -- * Types and Types
  , Sig (..), Type (..), TVar (..), Ctor (..)
  , RType (..)
  , Boolable (..)

  -- * Abstract syntax of Mist
  , Expr  (..)
  , Bind  (..)
  , Def

  , BareBind, BareRType, Bare, BareDef, BareSig

  , AnfExpr,   ImmExpr, AnfCore
  , Core  (..)
  , Prim (..)
  , AnnBind  (..)

  , Field (..)
  , Prim2 (..)

  , isAnf
  , isVarAnf
  , extract
  , extractC


  -- * Smart Constructors
  , bindsExpr
  , defsExpr
  , bindsRType
  , strengthen

  -- * Destructors
  , exprDefs

  , bkRType
  , eraseRType
  , reftRType

    -- * Environments
  , Env
  , emptyEnv
  , pushEnv
  , lookupEnv
  , memberEnv
  , addEnv
  , fromListEnv
  , envMax
  ) where

import           GHC.Exts( IsString(..) )
import           Prelude
import qualified Data.List        as L
import           Data.Maybe                       (isJust)
import           Text.Printf
import qualified Text.PrettyPrint  as PP
import           Language.Mist.UX

--------------------------------------------------------------------------------
-- | Abstract syntax of Mist
--------------------------------------------------------------------------------

-- | `Id` are program variables
type Id = Text

-- | `Prim2` are binary operations
data Prim2
  = Plus
  | Minus
  | Times
  | Less
  | Greater
  | Equal
  | And
  deriving (Show, Read)

-- | Expr are single expressions
data Expr a
  = Number  !Integer                                a
  | Boolean !Bool                                   a
  | Id      !Id                                     a
  | Prim2   !Prim2    !(Expr a) !(Expr a)           a
  | If      !(Expr a) !(Expr a) !(Expr a)           a
  | Let     !(Bind a) !(Sig  a) !(Expr a) !(Expr a) a
  | Tuple   !(Expr a) !(Expr a)                     a
  | GetItem !(Expr a) !Field                        a
  | App     !(Expr a) !(Expr a)                     a
  | Lam     !(Bind a) !(Expr a)                     a
  -- | KVar    !KVar     ![Id]                         a
  | Unit                                            a
    deriving (Show, Functor, Read)

-- | Core are expressions with explicit TAbs and TApp
-- and every binding annotated.
data Core a
  = CNumber  !Integer                         a
  | CBoolean !Bool                            a
  | CId      !Id                              a
  | CPrim2   !Prim2       !(Core a) !(Core a) a
  | CIf      !(Core a)    !(Core a) !(Core a) a
  | CLet     !(AnnBind a) !(Core a) !(Core a) a
  | CTuple   !(Core a)    !(Core a)           a
  | CPrim    !Prim                            a
  | CApp     !(Core a)    !(Core a)           a
  | CLam     !(AnnBind a) !(Core a)           a      -- TODO: change to single argument functions
  | CTApp    !(Core a)    !Type               a      -- TODO: should the type instantiation be a Type or an RType?
  | CTAbs    TVar         !(Core a)           a
  | CUnit                                     a
  deriving (Show, Functor, Read)

data Sig a
  = Infer
  | Check  (RType Expr a)
  | Assume (RType Expr a)
  deriving (Show, Functor, Read)

data Field
  = Zero
  | One
  deriving (Show, Read)

data Prim
  = Pi0
  | Pi1
  deriving (Show, Read)

data Bind a = Bind
  { bindId    :: !Id
  , bindLabel :: a
  }
  deriving (Show, Functor, Read)

data AnnBind a = AnnBind
  { aBindId :: !Id
  , aBindType :: !(RType Core a)
  , aBindLabel :: a
  }
  deriving (Show, Functor, Read)

type Def a = (Bind a, Sig a, Expr a)


-- | Constructing a function declaration
-- dec :: Bind a -> Sig -> [Bind a] -> Expr a -> Expr a -> a -> Expr a
-- dec f t xs e e' l = Let f (Fun f t xs e l) e' l

defsExpr :: Show a => [Def a] -> Expr a
defsExpr [] = error "list of defintions is empty"
defsExpr bs@((b,_,_):_)   = go (bindLabel b) bs
  where
    go l []               = Unit l
    go _ ((b, s, e) : ds) = Let b s e (go l ds) l where l = bindLabel b

-- | Constructing `Expr` from let-binds
bindsExpr :: [(Bind a, Expr a)] -> Expr a -> a -> Expr a
bindsExpr bs e l = foldr (\(x, e1) e2  -> Let x Infer e1 e2 l) e bs

-- | Constructing `RForall` from let-binds
bindsRType :: AnnBind a -> RType Core a -> RType Core a
bindsRType b t = mkPiCB b t

-- | makes a Pi type from a Core Binder and an RType
mkPiCB :: AnnBind a -> RType Core a -> RType Core a
mkPiCB (AnnBind x t l) (RForall a t') = RForall a (RFun (Bind x l) t t')
mkPiCB (AnnBind x t l) t' = RFun (Bind x l) t t'

-- | Destructing `Expr` into let-binds
exprDefs :: Expr a -> ([Def a], Expr a)
exprDefs = go
  where
    go (Let x s e e' _) = ((x, s, e) : bs, body) where  (bs, body) = go e'
    go body             = ([]            , body)

--------------------------------------------------------------------------------
extract :: Expr a -> a
--------------------------------------------------------------------------------
extract (Number _ l)    = l
extract (Boolean _ l)   = l
extract (Id _ l)        = l
extract (Prim2 _ _ _ l) = l
extract (If    _ _ _ l) = l
extract (Let _ _ _ _ l) = l
extract (App _ _ l)     = l
extract (Tuple _ _ l)   = l
extract (GetItem _ _ l) = l
extract (Lam _ _ l)     = l
extract (Unit  l)       = l

--------------------------------------------------------------------------------
extractC :: Core a -> a
--------------------------------------------------------------------------------
extractC (CNumber _ l)    = l
extractC (CBoolean _ l)   = l
extractC (CId _ l)        = l
extractC (CPrim2 _ _ _ l) = l
extractC (CIf    _ _ _ l) = l
extractC (CLet _ _ _ l)   = l
extractC (CApp _ _ l)     = l
extractC (CTuple _ _ l)   = l
extractC (CPrim _ l)   = l
extractC (CLam _ _ l)     = l
extractC (CUnit  l)       = l
extractC (CTApp _ _ l)    = l
extractC (CTAbs _ _ l)    = l

--------------------------------------------------------------------------------
-- | Dynamic Errors
--------------------------------------------------------------------------------

-- | DynError correspond to different kind of dynamic/run-time errors
data DynError
  = ArithOverflow
  | IndexLow
  | IndexHigh
  | ArityError
  deriving (Show)

--------------------------------------------------------------------------------
-- | Pretty Printer
--------------------------------------------------------------------------------
instance PPrint Prim2 where
  pprint Plus    = "+"
  pprint Minus   = "-"
  pprint Times   = "*"
  pprint Less    = "<"
  pprint Greater = ">"
  pprint Equal   = "=="
  pprint And     = "&&"

instance PPrint Bool where
  pprint True  = "True"
  pprint False = "False"

instance PPrint (Bind a) where
  pprint (Bind x _) = x

instance PPrint (AnnBind a) where
  pprint (AnnBind x _ _) = x

instance PPrint Field where
  pprint Zero  = "0"
  pprint One   = "1"

instance PPrint (Expr a) where
  pprint (Number n _)    = show n
  pprint (Boolean b _)   = pprint b
  pprint (Id x _)        = x
  pprint (Prim2 o l r _) = printf "%s %s %s"                (pprint l)      (pprint o) (pprint r)
  pprint (If    c t e _) = printf "(if %s then %s else %s)" (pprint c)      (pprint t) (pprint e)
  pprint e@Let{}      = printf "(let %s in %s)"          (ppDefs ds)     (pprint e') where (ds, e') = exprDefs e
  pprint (App e1 e2 _)   = printf "(%s %s)"                 (pprint e1)     (pprint e2)
  pprint (Tuple e1 e2 _) = printf "(%s, %s)"                (pprint e1)     (pprint e2)
  pprint (GetItem e i _) = printf "(%s[%s])"                (pprint e)      (pprint i)
  pprint (Lam x e _)     = printf "(\\ %s -> %s)"           (pprint x)      (pprint e)
  pprint (Unit _)        = "skip"

instance PPrint (Core a) where
  pprint (CNumber n _)    = show n
  pprint (CBoolean b _)   = pprint b
  pprint (CId x _)        = x
  pprint (CPrim2 o l r _) = printf "%s %s %s"                (pprint l)      (pprint o) (pprint r)
  pprint (CIf    c t e _) = printf "(if %s then %s else %s)" (pprint c)      (pprint t) (pprint e)
  pprint (CApp e1 e2 _)   = printf "(%s %s)"                 (pprint e1)     (pprint e2)
  pprint (CTuple e1 e2 _) = printf "(%s, %s)"                (pprint e1)     (pprint e2)
  pprint (CPrim prim _)   = printf "%s"                      (pprint prim)
  pprint (CLam x e _)     = printf "(\\ %s -> %s)"           (pprint x)      (pprint e)
  pprint (CUnit _)        = "()"
  pprint _                = "TODO PPrint Core"

instance PPrint Prim where
  pprint Pi0              = "π0"
  pprint Pi1              = "π1"

ppDefs :: [Def a] -> Text
ppDefs = L.intercalate "\n " . fmap ppDef

ppDef :: Def a -> Text
ppDef (b, Check s , e) = ppSig "::" b s ++ ppEqn b e
ppDef (b, Assume s, e) = ppSig "as" b s ++ ppEqn b e
ppDef (b, Infer   , e) =                   ppEqn b e

ppSig k b s = printf "%s %s %s\n" (pprint b) k (pprint s)
ppEqn b e    = printf "%s = \n" (pprint b)
            ++ nest 2           (pprint e)

nest       :: Int -> Text -> Text
nest n     = unlines . map pad . lines
  where
    pad s  = blanks ++ s
    blanks = replicate n ' '

instance PPrint (e a) => PPrint (RType e a) where
  pprint (RBase b t e) =
    printf "{%s:%s | %s}" (pprint b) (pprint t) (pprint e)
  pprint (RFun b t1 t2) =
    printf "%s:%s -> %s" (pprint b) (pprint t1) (pprint t2)
  pprint (RRTy b t e) =
    printf "{%s:%s || %s}" (pprint b) (pprint t) (pprint e)
  pprint (RForall tv t) = printf "forall %s. %s" (pprint tv) (pprint t)

--------------------------------------------------------------------------------
-- | `isAnf e` is True if `e` is an A-Normal Form
--------------------------------------------------------------------------------
{-@ measure isAnf @-}
isAnf :: Expr a -> Bool
isAnf (Unit _)         = True
isAnf (Number  _ _)    = True
isAnf (Boolean _ _)    = True
isAnf (Id      _ _)    = True
isAnf (Prim2 _ e e' _) = isImm e && isImm e'
isAnf (If c t e _)     = isImm c && isAnf t && isAnf e
isAnf (Let _ _ e e' _) = isAnf e && isAnf e'
isAnf (Tuple e e' _)   = isAnf e && isAnf e'
isAnf (GetItem e _ _)  = isAnf e
isAnf (App e e' _)     = isAnf e  && isAnf e'
isAnf (Lam _ e _)      = isAnf e

{-@ measure isImm @-}
isImm :: Expr a -> Bool
isImm (Number  _ _) = True
isImm (Boolean _ _) = True
isImm (Id      _ _) = True
isImm _             = False

{-@ type AnfExpr a = {v:Expr a| isAnf v} @-}
type AnfExpr = Expr

{-@ type ImmExpr a = {v:Expr a | isImm v} @-}
type ImmExpr = Expr

-- ANF for core is a little stricter; instead of immediates, we want functions
-- to be applied only to vars

{-@ type AnfCore a = {v:(Core a) | isVarAnf v } @-}
type AnfCore a = Core a

{-@ measure isVarAnf @-}
isVarAnf :: Expr a -> Bool
isVarAnf (Unit _)         = True
isVarAnf (Number  _ _)    = True
isVarAnf (Boolean _ _)    = True
isVarAnf (Id      _ _)    = True
isVarAnf (Prim2 _ e e' _) = isVar e && isVar e'
isVarAnf (If c t e _)     = isVar c && isVarAnf t && isVarAnf e
isVarAnf (Let _ _ e e' _) = isVarAnf e && isVarAnf e'
isVarAnf (Tuple e e' _)   = isVarAnf e && isVarAnf e'
isVarAnf (GetItem e _ _)  = isVarAnf e
isVarAnf (App e e' _)     = isVarAnf e  && isVar e'
isVarAnf (Lam _ e _)      = isVarAnf e

{-@ measure isVar @-}
isVar :: Expr a -> Bool
isVar (Id      _ _) = True
isVar _             = False


--------------------------------------------------------------------------------
-- | The `Bare` types are for parsed ASTs.
--------------------------------------------------------------------------------

type Bare     = Expr SourceSpan
type BareRType = RType Expr SourceSpan
type BareBind = Bind SourceSpan
type BareDef  = Def  SourceSpan
type BareSig  = Sig  SourceSpan

instance Located Bare where
  sourceSpan = extract

instance Located BareBind where
  sourceSpan (Bind _ l) = l

--------------------------------------------------------------------------------
-- | Functions for accessing the "environment" (stack)
--------------------------------------------------------------------------------

-- | An `Env` is a lookup-table mapping `Id` to some Int value
data Env = Env { envBinds :: [(Id, Int)]
               , envMax   :: !Int
               }
           deriving (Show)

emptyEnv :: Env
emptyEnv = Env [] 0

lookupEnv :: Id -> Env -> Maybe Int
lookupEnv k env = lookup k (envBinds env)

memberEnv :: Id -> Env -> Bool
memberEnv k env = isJust (lookupEnv k env)

pushEnv :: Bind a -> Env -> (Int, Env)
pushEnv x (Env bs n) = (n', Env bs' n')
  where
    bs'              = (bindId x, n') : bs
    n'               = 1 + n

addEnv :: Bind a -> Env -> Env
addEnv x env = snd (pushEnv x env)

fromListEnv :: [(Id, Int)] -> Env
fromListEnv bs = Env bs n
  where
    n          = maximum (0 : [i | (_, i) <- bs])

--------------------------------------------------------------------------------
-- | Types, Environments -------------------------------------------------------
--------------------------------------------------------------------------------

-- | Refinement types
-- | - refinements are expressions of type Bool
-- |
-- | ```
-- | τ ::= { v:τ | r }   -- a refinement on an RType
-- |     | { v:b | r }   -- a refinement on a base Type
-- |     | x:τ -> τ      -- a pi type
-- | ```
-- |
-- | This allows us to bind functions as in LH `--higherorder`
-- |   {f : { v:_ | v < 0 } -> { v:_ | v > 0} | f 0 = 0}

data RType e a
  = RBase !(Bind a) Type !(e a)
  | RFun !(Bind a) !(RType e a) !(RType e a)
  | RRTy !(Bind a) !(RType e a) !(e a)
  | RForall TVar !(RType e a)
  deriving (Show, Functor, Read)

data Type = TVar TVar           -- a
          | TUnit               -- 1
          | TInt                -- Int
          | TBool               -- Bool
          | Type :=> Type       -- t1 => t2
          | TPair Type Type     -- (t0, t1)
          | TCtor Ctor [Type]   -- Ctor [t1,...,tn]
          | TForall TVar Type   -- ∀a.t
          deriving (Eq, Ord, Show, Read)

newtype Ctor = CT Id deriving (Eq, Ord, Show, Read)

newtype TVar = TV Id deriving (Eq, Ord, Show, Read)

class Strengthable e a | a -> e where
  strengthen :: e -> a -> a

instance Strengthable (Expr a) (Expr a) where
  strengthen q p = Prim2 And p q (extract p)

instance Strengthable (Core a) (Core a) where
  strengthen q p = CPrim2 And p q (extractC p)

instance Strengthable (e a) (e a) => Strengthable (e a) (RType e a) where
  strengthen q (RBase v t p) = RBase v t (strengthen q p)
  strengthen q (RRTy v t p) = RRTy v t (strengthen q p)
  strengthen q (RFun v t p) = RFun v (strengthen q t) p
  strengthen q (RForall tvs rt) = RForall tvs $ strengthen q rt

class Boolable a l where
    true :: l -> a
    _false :: l -> a

instance Boolable (Core a) a where
    true = CBoolean True
    _false = CBoolean False

instance Boolable (Expr a) a where
    true = Boolean True
    _false = Boolean False


-- | Breaks up an RType into an binder, sort, and refinement
bkRType :: (Strengthable (e a) (e a), Boolable (e a) a)
          => RType e a -> (String, Type, e a, a)
bkRType rt = (bindRType rt, eraseRType rt, reftRType rt, tagRType rt)

bindRType :: RType e a -> String
bindRType (RBase (Bind x _) _ _) = x
bindRType (RFun  (Bind x _) _ _) = x
bindRType (RRTy  (Bind x _) _ _) = x
bindRType (RForall _ rt) =  bindRType rt

-- | Returns the base type for an RType
eraseRType :: RType e a -> Type
eraseRType (RBase _ t _) = t
eraseRType (RFun _ t1 t2) = eraseRType t1 :=> eraseRType t2
eraseRType (RRTy _ t _) = eraseRType t
eraseRType (RForall alphas t) = TForall alphas (eraseRType t)

-- | Returns the refinement of an RType
reftRType :: (Strengthable (e a) (e a), Boolable (e a) a)
          => RType e a -> e a
reftRType (RRTy _ rt r)  = strengthen r (reftRType rt)
reftRType (RBase _ _ r)  = r
reftRType (RForall _ rt) = reftRType rt
reftRType (RFun (Bind _ l) _ _) = true l

tagRType :: (Strengthable (e a) (e a), Boolable (e a) a)
         => RType e a -> a
tagRType (RRTy (Bind _ l) _ _)  = l
tagRType (RBase (Bind _ l) _ _)  = l
tagRType (RForall _ rt) = tagRType rt
tagRType (RFun (Bind _ l) _ _) = l

instance PPrint Ctor where
  pprint = PP.render . prCtor

instance PPrint TVar where
  pprint = PP.render . prTVar

instance PPrint Type where
  pprint = PP.render . prType

instance IsString TVar where
  fromString = TV

instance IsString Type where
  fromString = TVar . TV

prType            :: Type -> PP.Doc
prType TUnit        = PP.text "Unit"
prType (TVar a)     = prTVar a
prType TInt         = PP.text "Int"
prType TBool        = PP.text "Bool"
prType (t1 :=> t2)   = PP.parens (prType t1) PP.<+> PP.text "=>" PP.<+> prType t2
prType (TPair t s)  = PP.parens $ prType t PP.<> PP.text "," PP.<+> prType s
prType (TCtor c ts) = prCtor c PP.<> PP.brackets (prTypes ts)
prType (TForall a t)  = PP.text "Forall" PP.<+>
                          prTVar a
                          PP.<> PP.text "." PP.<+> prType t

prTypes           :: [Type] -> PP.Doc
prTypes ts         = PP.hsep $ PP.punctuate PP.comma (prType <$> ts)


prCtor :: Ctor -> PP.Doc
prCtor (CT c) = PP.text c

prTVar :: TVar -> PP.Doc
prTVar (TV a) = PP.text a
