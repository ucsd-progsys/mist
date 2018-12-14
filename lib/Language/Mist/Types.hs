{-# LANGUAGE DeriveFunctor        #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances    #-}

module Language.Mist.Types
  (
  -- * Re-Export SourceSpans
    module Language.Mist.UX

  -- * Aliases for various identifiers
  , Id

  -- * Types and Polys
  , Sig (..), Type (..), Poly (..), TVar (..), Ctor (..)
  , RType (..), RPoly (..)

  -- * Abstract syntax of Mist
  , Expr  (..)
  , Bind  (..)
  , Def

  , BareBind, BareType, BarePoly, Bare, BareDef, BareSig

  , AnfExpr,   ImmExpr, AnfCore
  , Core  (..)
  , AnnBind  (..)

  , Field (..)
  , Prim2 (..)

  , isAnf
  , isVarAnf
  , extract


  -- * Smart Constructors
  , bindsExpr
  , defsExpr
  , bindsRType

  -- * Destructors
  , exprDefs

  , eraseRPoly
  , eraseRType

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
  | Lam     [Bind a]  !(Expr a)                     a
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
  | CGetItem !(Core a)    !Field              a
  | CApp     !(Core a)    !(Core a)           a
  | CLam     [AnnBind a]  !(Core a)           a      -- TODO: change to single argument functions
  | CTApp    !(Core a)    !Type               a      -- TODO: should the type instantiation be a Type or an RType?
  | CTAbs    [TVar]       !(Core a)           a
  | CUnit                                     a
  deriving (Show, Functor, Read)

data Sig a
  = Infer
  | Check  (RPoly a)
  | Assume (RPoly a)
    deriving (Show, Functor, Read)

data Field
  = Zero
  | One
    deriving (Show, Read)

data Bind a = Bind
  { bindId    :: !Id
  , bindLabel :: a
  }
  deriving (Show, Functor, Read)

data AnnBind a = AnnBind
  { aBindId :: !Id
  , aBindType :: !(RPoly a)
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

-- | Constructing `RPoly` from let-binds
bindsRType :: [AnnBind a] -> RPoly a -> RPoly a
bindsRType bs t = foldr mkPiCB t bs

mkPiCB :: AnnBind a -> RPoly a -> RPoly a
mkPiCB (AnnBind x t l) (RForall as t') = RForall as (RFun (Bind x l) tmono t')
  where RForall [] tmono = t

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

instance PPrint Bool where
  pprint True  = "True"
  pprint False = "False"

instance PPrint (Bind a) where
  pprint (Bind x _) = x

instance PPrint Field where
  pprint Zero  = "0"
  pprint One   = "1"

instance PPrint (Expr a) where
  pprint (Number n _)    = show n
  pprint (Boolean b _)   = pprint b
  pprint (Id x _)        = x
  pprint (Prim2 o l r _) = printf "%s %s %s"                (pprint l)      (pprint o) (pprint r)
  pprint (If    c t e _) = printf "(if %s then %s else %s)" (pprint c)      (pprint t) (pprint e)
  pprint e@(Let {})      = printf "(let %s in %s)"          (ppDefs ds)     (pprint e') where (ds, e') = exprDefs e
  pprint (App e1 e2 _)   = printf "(%s %s)"                 (pprint e1)     (pprint e2)
  pprint (Tuple e1 e2 _) = printf "(%s, %s)"                (pprint e1)     (pprint e2)
  pprint (GetItem e i _) = printf "(%s[%s])"                (pprint e)      (pprint i)
  pprint (Lam xs e _)    = printf "(\\ %s -> %s)"           (ppMany " " xs) (pprint e)
  pprint (Unit _)        = "skip"

ppMany :: (PPrint a) => Text -> [a] -> Text
ppMany sep = L.intercalate sep . fmap pprint

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

instance PPrint (RPoly a) where
  pprint (RForall [] t)  = pprint t
  pprint (RForall tvs t) = printf "forall %s. %s" (ppMany " " tvs) (pprint t)

instance PPrint (RType a) where
  pprint (RBase b t e) =
    printf "{%s:%s | %s}" (pprint b) (pprint t) (pprint e)
  pprint (RFun b t1 t2) =
    printf "%s:%s -> %s" (pprint b) (pprint t1) (pprint t2)
  pprint (RRTy b t e) =
    printf "{%s:%s || %s}" (pprint b) (pprint t) (pprint e)

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
type BareType = RType SourceSpan
type BarePoly = RPoly SourceSpan
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

data RType a
  = RBase !(Bind a) Type !(Expr a)
  | RFun !(Bind a) !(RType a) !(RType a)
  | RRTy !(Bind a) !(RType a) !(Expr a)
  deriving (Show, Functor, Read)

data Type =  TVar TVar          -- a
          |  TInt               -- Int
          |  TBool              -- Bool
          |  [Type] :=> Type    -- (t1,...,tn) => t2               TODO: make currying the only option
          |  TPair Type Type    -- (t0, t1)
          |  TCtor Ctor [Type]  -- Ctor [t1,...,tn]
          deriving (Eq, Ord, Show, Read)

newtype Ctor = CT Id deriving (Eq, Ord, Show, Read)

newtype TVar = TV Id deriving (Eq, Ord, Show, Read)

data Poly = Forall [TVar] Type       -- forall a. t
  deriving (Show, Read)

data RPoly a =  RForall [TVar] (RType a) deriving (Show, Functor, Read)

eraseRPoly :: RPoly a -> Poly
eraseRPoly (RForall alphas t) = Forall alphas (eraseRType t)

eraseRType :: RType a -> Type
eraseRType (RBase _ t _) = t
eraseRType (RFun _ t1 t2) = [(eraseRType t1)] :=> (eraseRType t2)
eraseRType (RRTy _ t _) = eraseRType t

instance PPrint Ctor where
  pprint = PP.render . prCtor

instance PPrint TVar where
  pprint = PP.render . prTVar

instance PPrint Type where
  pprint = PP.render . prType

instance PPrint Poly where
  pprint = PP.render . prPoly

instance IsString TVar where
  fromString = TV

instance IsString Type where
  fromString = TVar . TV

prType            :: Type -> PP.Doc
prType (TVar a)     = prTVar a
prType TInt         = PP.text "Int"
prType TBool        = PP.text "Bool"
prType (ts :=> t)   = PP.parens (prTypes ts) PP.<+> PP.text "=>" PP.<+> prType t
prType (TPair t s)  = PP.parens $ prType t PP.<> PP.text "," PP.<+> prType s
prType (TCtor c ts) = prCtor c PP.<> PP.brackets (prTypes ts)

prTypes           :: [Type] -> PP.Doc
prTypes ts         = PP.hsep $ PP.punctuate PP.comma (prType <$> ts)


prCtor :: Ctor -> PP.Doc
prCtor (CT c) = PP.text c

prTVar :: TVar -> PP.Doc
prTVar (TV a) = PP.text a

prPoly                ::  Poly -> PP.Doc
prPoly (Forall [] t)  = prType t
prPoly (Forall as t)  = PP.text "Forall" PP.<+>
                          PP.hcat (PP.punctuate PP.comma (map prTVar as))
                          PP.<> PP.text "." PP.<+> prType t
