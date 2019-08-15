{-# LANGUAGE DeriveFunctor        #-}
{-# LANGUAGE GeneralizedNewtypeDeriving        #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PatternSynonyms #-}

module Language.Mist.Types
  (
  -- * Re-Export SourceSpans
    module Language.Mist.UX

  -- * Aliases for various identifiers
  , Id

  -- * Types and Types
  , Type (..), TVar (..), Ctor (..)
  , RType (..)
  , Variance (..)

  , Measures
  
  -- * Built-in Types
  , setType
  , mapType

  -- * Abstract syntax of Mist
  , Expr (..)
  , Bind (..)

  , pattern Number
  , pattern Boolean
  , pattern Unit
  , pattern Id
  , pattern Prim
  , pattern If
  , pattern Let
  , pattern Lam
  , pattern App
  , pattern TApp
  , pattern TAbs
  , pattern Bind

  , ParsedAnnotation (..)
  , ParsedExpr, ParsedBind
  , SSParsedExpr (..)

  , ElaboratedAnnotation (..)
  , ElaboratedExpr, ElaboratedBind

  , AnfExpr
  , ImmExpr

  , Prim (..)

  , extractLoc, extractAnn
  , putAnn
  , unTV

  , eraseRType

  , Subst

  , NNF (..)
  , Predicate (..)

  , MonadFresh (..)
  , Default (..)
  ) where

import GHC.Exts (IsString(..))
import Prelude
import Text.Printf
import qualified Text.PrettyPrint as PP
import Language.Mist.UX
import Data.Bifunctor
import Data.List (intercalate)
import qualified Data.Map as M

import Control.Monad.State
import Control.Monad.Writer
import Control.Monad.Identity
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.Cont

--------------------------------------------------------------------------------
-- | Abstract syntax of Mist
--------------------------------------------------------------------------------

-- | `Id` are program variables
type Id = Text

data Prim
  = Plus
  | Minus
  | Times
  | Less
  | Greater
  | Lte
  | Equal
  | And
  | Elem
  | Union
  | SetAdd
  | SetDel
  | SetSub
  | Store
  | Select
  deriving (Show, Eq, Read)

-- | Mist expressions
-- Parameterized by the type of annotations
-- and the extra data.
data Expr t a
  = AnnNumber !Integer !t !a
  | AnnBoolean !Bool !t !a
  | AnnUnit !t !a
  | AnnId !Id !t !a
  | AnnPrim !Prim !t !a
  | AnnIf !(Expr t a) !(Expr t a) !(Expr t a) !t !a
  | AnnLet !(Bind t a) !(Expr t a) !(Expr t a) !t !a
  | AnnApp !(Expr t a) !(Expr t a) !t !a
  | AnnLam !(Bind t a) !(Expr t a) !t !a
  | AnnTApp !(Expr t a) !Type !t !a
  | AnnTAbs TVar !(Expr t a) !t !a
  deriving (Show, Functor, Eq, Read)

data Bind t a = AnnBind
  { bindId :: !Id
  , bindAnn :: !t
  , bindTag :: !a
  }
  deriving (Show, Functor, Eq, Read)

{-# COMPLETE Number, Boolean, Unit, Id, Prim, If, Let, Lam, App, TApp, TAbs #-}

pattern Number :: (Default t) => Integer -> a -> Expr t a
pattern Number n l <- AnnNumber n _ l
  where Number n l = AnnNumber n defaultVal l
pattern Boolean :: (Default t) => Bool -> a -> Expr t a
pattern Boolean b l <- AnnBoolean b _ l
  where Boolean b l = AnnBoolean b defaultVal l
pattern Unit :: (Default t) => a -> Expr t a
pattern Unit l <- AnnUnit _ l
  where Unit l = AnnUnit defaultVal l
pattern Id :: (Default t) => Id -> a -> Expr t a
pattern Id x l <- AnnId x _ l
  where Id x l = AnnId x defaultVal l
pattern Prim :: (Default t) => Prim -> a -> Expr t a
pattern Prim op l <- AnnPrim op _ l
  where Prim op l = AnnPrim op defaultVal l
pattern If :: (Default t) => Expr t a -> Expr t a -> Expr t a -> a -> Expr t a
pattern If e1 e2 e3 l <- AnnIf e1 e2 e3 _ l
  where If e1 e2 e3 l = AnnIf e1 e2 e3 defaultVal l
pattern Let :: (Default t) => Bind t a -> Expr t a -> Expr t a -> a -> Expr t a
pattern Let x e1 e2 l <- AnnLet x e1 e2 _ l
  where Let x e1 e2 l = AnnLet x e1 e2 defaultVal l
pattern Lam :: (Default t) => Bind t a -> Expr t a -> a -> Expr t a
pattern Lam x e l <- AnnLam x e _ l
  where Lam x e l = AnnLam x e defaultVal l
pattern App :: (Default t) => Expr t a -> Expr t a -> a -> Expr t a
pattern App e1 e2 l <- AnnApp e1 e2 _ l
  where App e1 e2 l = AnnApp e1 e2 defaultVal l
pattern TApp :: (Default t) => Expr t a -> Type -> a -> Expr t a
pattern TApp e typ l <- AnnTApp e typ _ l
  where TApp e typ l = AnnTApp e typ defaultVal l
pattern TAbs :: (Default t) => TVar -> Expr t a -> a -> Expr t a
pattern TAbs tvar e l <- AnnTAbs tvar e _ l
  where TAbs tvar e l = AnnTAbs tvar e defaultVal l

{-# COMPLETE Bind #-}

pattern Bind :: (Default t) => Id -> a -> Bind t a
pattern Bind id tag <- AnnBind id _ tag
  where Bind id tag = AnnBind id defaultVal tag

-- | Refinement types
-- | - refinements are expressions of type Bool
-- |
-- | ```
-- | τ ::= { v:τ | r }   -- a refinement on an RType
-- |     | { v:b | r }   -- a refinement on a base Type
-- |     | x:τ -> τ      -- a pi type
-- |     | ∀a.τ
-- | ```
-- |
-- | This allows us to bind functions as in LH `--higherorder`
-- |   {f : { v:_ | v < 0 } -> { v:_ | v > 0} | f 0 = 0}

-- TODO: add type variables
data RType r a
  = RBase !(Bind () a) Type !r
  | RApp !Ctor ![(Variance, RType r a)]
  | RFun !(Bind () a) !(RType r a) !(RType r a)
  | RIFun !(Bind () a) !(RType r a) !(RType r a)
  | RRTy !(Bind () a) !(RType r a) r
  | RForall TVar !(RType r a)
  | RForallP TVar !(RType r a)
  deriving (Show, Functor, Read)

data Type = TVar TVar           -- a
          | TUnit               -- 1
          | TInt                -- Int
          | TBool               -- Bool
          | Type :=> Type       -- t1 => t2
          | TCtor Ctor [(Variance, Type)]   -- Ctor [t1,...,tn]
          | TForall TVar Type   -- ∀a.t
          deriving (Eq, Ord, Show, Read)

newtype Ctor = CT Id deriving (Eq, Ord, Show, Read, IsString)

newtype TVar = TV Id deriving (Eq, Ord, Show, Read)

data Variance = Invariant | Bivariant | Contravariant | Covariant
              deriving (Show, Eq, Ord, Read)

type Measures = M.Map Id Type

setType :: Type -> Type
setType t = TCtor (CT "Set") [(Covariant, t)]

mapType :: Type -> Type -> Type
mapType t t'= TCtor (CT "Set") [(Contravariant, t), (Covariant, t')]

-- | The type of Mist type annotations after parsing
-- r is the type of refinements
data ParsedAnnotation r a
  = ParsedCheck !(RType r a)
  | ParsedAssume !(RType r a)
  | ParsedInfer
  deriving (Functor, Show, Read)

type ParsedExpr r a = Expr (Maybe (ParsedAnnotation r a)) a
type ParsedBind r a = Bind (Maybe (ParsedAnnotation r a)) a
newtype SSParsedExpr = SSParsedExpr { unSSParsedExpr :: ParsedExpr SSParsedExpr SourceSpan } deriving Read

-- | The type of Mist type annotations after elaboration
-- r is the type of refinements
data ElaboratedAnnotation r a
  = ElabRefined !(RType r a)
  | ElabAssume !(RType r a)
  | ElabUnrefined !Type
  deriving (Functor, Show)

type ElaboratedExpr r a = Expr (Maybe (ElaboratedAnnotation r a)) a
type ElaboratedBind r a = Bind (Maybe (ElaboratedAnnotation r a)) a

type AnfExpr t a = Expr t a
type ImmExpr t a = Expr t a

-- -- | Constructing a function declaration
-- dec :: Bind a -> Sig -> [Bind a] -> Expr a -> Expr a -> a -> Expr a
-- dec f t xs e e' l = Let f (Fun f t xs e l) e' l

-- | Constructing `RForall` from let-binds
-- bindsRType :: AnnBind a -> RType Core a -> RType Core a
-- bindsRType b t = mkPiCB b t

-- | makes a Pi type from a Core Binder and an RType
-- mkPiCB :: AnnBind a -> RType Core a -> RType Core a
-- mkPiCB (AnnBind x t l) (RForall a t') = RForall a (RFun (Bind x l) t t')
-- mkPiCB (AnnBind x t l) t' = RFun (Bind x l) t t'

-- | Destructing `Expr` into let-binds
-- exprDefs :: Expr a t -> ([Def a t], Expr a t)
-- exprDefs = go
--   where
--     go (Let x e e' _) = ((x, e) : bs, body)
--       where (bs, body) = go e'
--     go body = ([], body)

extractLoc :: Expr t a -> a
extractLoc (AnnNumber _ _ l)    = l
extractLoc (AnnBoolean _ _ l)   = l
extractLoc (AnnId _ _ l)        = l
extractLoc (AnnPrim _ _ l)      = l
extractLoc (AnnIf _ _ _ _ l)    = l
extractLoc (AnnLet _ _ _ _ l)   = l
extractLoc (AnnApp _ _ _ l)     = l
extractLoc (AnnLam _ _ _ l)     = l
extractLoc (AnnUnit _ l)        = l
extractLoc (AnnTApp _ _ _ l)    = l
extractLoc (AnnTAbs _ _ _ l)    = l

extractAnn :: Expr t a -> t
extractAnn (AnnNumber _ t _)    = t
extractAnn (AnnBoolean _ t _)   = t
extractAnn (AnnId _ t _)        = t
extractAnn (AnnPrim _ t _)      = t
extractAnn (AnnIf _ _ _ t _)    = t
extractAnn (AnnLet _ _ _ t _)   = t
extractAnn (AnnApp _ _ t _)     = t
extractAnn (AnnLam _ _ t _)     = t
extractAnn (AnnUnit t _)        = t
extractAnn (AnnTApp _ _ t _)    = t
extractAnn (AnnTAbs _ _ t _)    = t

putAnn :: t -> Expr t a -> Expr t a
putAnn t (AnnNumber n _ l) = AnnNumber n t l
putAnn t (AnnBoolean b _ l) = AnnBoolean b t l
putAnn t (AnnId x _ l) = AnnId x t l
putAnn t (AnnPrim p _ l) = AnnPrim p t l
putAnn t (AnnIf e1 e2 e3 _ l) = AnnIf e1 e2 e3 t l
putAnn t (AnnLet x e1 e2 _ l) = AnnLet x e1 e2 t l
putAnn t (AnnApp e1 e2 _ l) = AnnApp e1 e2 t l
putAnn t (AnnLam x e _ l) = AnnLam x e t l
putAnn t (AnnUnit _ l) = AnnUnit t l
putAnn t (AnnTApp e typ _ l) = AnnTApp e typ t l
putAnn t (AnnTAbs tvar e _ l) = AnnTAbs tvar e t l

--------------------------------------------------------------------------------
-- | Pretty Printer
--------------------------------------------------------------------------------

instance PPrint Prim where
  pprint Plus    = "+"
  pprint Minus   = "-"
  pprint Times   = "*"
  pprint Less    = "<"
  pprint Greater = ">"
  pprint Lte     = ">="
  pprint Equal   = "=="
  pprint And     = "&&"
  pprint Elem    = "∈"
  pprint Union   = "∪"
  pprint SetDel  = "setMinus"
  pprint SetAdd  = "setAdd"
  pprint SetSub  = "setSubset"
  pprint Store  = "store"
  pprint Select  = "select"

instance PPrint Bool where
  pprint True  = "True"
  pprint False = "False"

instance PPrint () where
  pprint () = ""

instance PPrint a => PPrint (Maybe a) where
  pprint Nothing = ""
  pprint (Just a) = pprint a

-- TODO: properly print annotations
instance (PPrint t) => PPrint (Bind t a) where
  pprint (AnnBind x tag _) = printf "%s %s" x (pprint tag)

instance (PPrint r) => PPrint (ElaboratedAnnotation r a) where
  pprint (ElabRefined rtype) = printf " : %s" (pprint rtype)
  pprint (ElabAssume rtype) = printf " as %s" (pprint rtype)
  pprint (ElabUnrefined typ) = printf " : %s" (pprint typ)

instance (PPrint r) => PPrint (ParsedAnnotation r a) where
  pprint (ParsedCheck rtype) = printf " : %s" (pprint rtype)
  pprint (ParsedAssume rtype) = printf " as %s" (pprint rtype)
  pprint ParsedInfer = ""

-- TODO: better instance
instance (PPrint t) => PPrint (Expr t a) where
  pprint (AnnNumber n _ _) = show n
  pprint (AnnBoolean b _ _) = pprint b
  pprint (AnnUnit _ _) = "()"
  pprint (AnnId x _ _) = x
  pprint (AnnPrim o _ _) = printf "%s" (pprint o)
  pprint (AnnIf c t e _ _) = printf "(if %s then %s else %s)" (pprint c) (pprint t) (pprint e)
  -- pprinAnnt e@Let{} = printf "(let %s in %s)" (ppDefs ds) (pprint e')
  --   wheAnnre (ds, e') = exprDefs e
  pprint (AnnLet bind e1 e2 _ _) = printf "(let %s = %s in %s)" (ppDef bind) (pprint e1) (pprint e2)-- TODO: make better
  pprint (AnnApp e1 e2 _ _) = printf "(%s %s)" (pprint e1) (pprint e2)
  pprint (AnnLam x e _ _) = printf "(\\ %s -> %s)" (ppDef x) (pprint e)
  pprint (AnnTApp e t _ _) = printf "(%s @ %s)" (pprint e) (pprint t)
  pprint (AnnTAbs alpha e _ _) = printf "(/\\%s . %s)" (pprint alpha) (pprint e)

ppDef :: (PPrint t) => Bind t a -> Text
ppDef annBind = printf "%s%s" (bindId annBind) (pprint $ bindAnn annBind)

_ppSig k b s = printf "%s %s %s\n" (pprint b) k (pprint s)
_ppEqn b e = printf "%s = \n" (pprint b)
            ++ nest 2 (pprint e)

nest :: Int -> Text -> Text
nest n = unlines . map pad . lines
  where
    pad s = blanks ++ s
    blanks = replicate n ' '

instance (PPrint r) => PPrint (RType r a) where
  pprint (RBase b t e) =
    printf "{%s:%s | %s}" (pprint b) (pprint t) (pprint e)
  pprint (RApp c ts) =
    printf "%s [%s]" (pprint c) (intercalate "," $ pprint <$> (snd <$> ts))
  pprint (RFun b t1 t2) =
    printf "%s:%s -> %s" (pprint b) (pprint t1) (pprint t2)
  pprint (RIFun b t1 t2) =
    printf "%s:%s ~> %s" (pprint b) (pprint t1) (pprint t2)
  pprint (RRTy b t e) =
    printf "{%s:%s || %s}" (pprint b) (pprint t) (pprint e)
  pprint (RForall tv t) = printf "forall %s. %s" (pprint tv) (pprint t)
  pprint (RForallP tv t) = printf "rforall %s. %s" (pprint tv) (pprint t)

--------------------------------------------------------------------------------
-- | The `Parsed` types are for parsed ASTs.
--------------------------------------------------------------------------------

instance Located a => Located (Expr t a) where
  sourceSpan e = sourceSpan $ extractLoc e

instance Located a => Located (Bind t a) where
  sourceSpan bind = sourceSpan $ bindTag bind

--------------------------------------------------------------------------------
-- | Types ---------------------------------------------------------------------
--------------------------------------------------------------------------------

unTV :: TVar -> Id
unTV (TV t) = t

-- | Returns the base type for an RType
eraseRType :: RType e a -> Type
eraseRType (RBase _ t _) = t
eraseRType (RApp c ts) = TCtor c $ second eraseRType <$> ts
eraseRType (RFun _ t1 t2) = eraseRType t1 :=> eraseRType t2
eraseRType (RIFun _ _t1 t2) = eraseRType t2
eraseRType (RRTy _ t _) = eraseRType t
eraseRType (RForall alphas t) = TForall alphas (eraseRType t)
eraseRType (RForallP alphas t) = TForall alphas (eraseRType t)

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

prType :: Type -> PP.Doc
prType TUnit        = PP.text "Unit"
prType (TVar a)     = prTVar a
prType TInt         = PP.text "Int"
prType TBool        = PP.text "Bool"
prType (t1 :=> t2)   = PP.parens (prType t1) PP.<+> PP.text "=>" PP.<+> prType t2
-- prType (TPair t s)  = PP.parens $ prType t PP.<> PP.text "," PP.<+> prType s
prType (TCtor c ts) = prCtor c PP.<> PP.braces (prTypeArgs ts)
prType (TForall a t)  = PP.text "Forall" PP.<+>
                          prTVar a
                          PP.<> PP.text "." PP.<+> prType t

prTypeArgs           :: [(Variance,Type)] -> PP.Doc
prTypeArgs ts         = PP.hsep $ PP.punctuate PP.comma (prType . snd <$> ts)


prCtor :: Ctor -> PP.Doc
prCtor (CT c) = PP.text c

prTVar :: TVar -> PP.Doc
prTVar (TV a) = PP.text a

--------------------------------------------------------------------------------
-- | Substitution Data Structure -----------------------------------------------
--------------------------------------------------------------------------------

type Subst e = M.Map Id e


--------------------------------------------------------------------------------
-- | Horn Clause Structures ----------------------------------------------------
--------------------------------------------------------------------------------

-- | NNF Constraints
data NNF r
  = Head r                             -- ^ p
  | CAnd [NNF r]                -- ^ c1 /\ c2
  | All Id Type r (NNF r)       -- ^ ∀x:τ.p => c
  | Any Id Type r (NNF r)       -- ^ :x:τ.p => c
  deriving (Show, Functor, Eq)

-- | Type class to represent predicates
class Predicate r where
  true :: r
  false :: r
  var ::  Id -> r
  varNot ::  Id -> r
  varsEqual :: Id -> Id -> r -- ^ builds a refinement that the two variables are equivalent
  prim :: (MonadFresh m) => Expr t a -> m (RType r a) -- ^ Gives a specification to primitives
                                                      -- TODO: this is a partial function
  strengthen :: r -> r -> r
  varSubst :: Subst Id -> r -> r -- ^ [x/y]r
  buildKvar :: Id -> [Id] -> r -- ^ k(x1, ..., xn)


instance Predicate () where
    true = ()
    false = ()
    var _ = ()
    varNot _ = ()
    varsEqual _ _ = ()
    prim _ = undefined

    strengthen _ _ = ()
    varSubst _ _ = ()
    buildKvar _ _ = ()

--------------------------------------------------------------------------------
-- | A MonadFresh encompasses the operations for generating fresh, scoped names
--------------------------------------------------------------------------------
class Monad m => MonadFresh m where
  refreshId :: Id -> m Id

-- TODO: figure out how to put this back in Names.hs

-------------------------------------------------------------------------------
-- MonadFresh instances -------------------------------------------------------
-------------------------------------------------------------------------------

instance (Monoid w, MonadFresh m) => MonadFresh (WriterT w m) where
  refreshId = lift . refreshId

instance MonadFresh m => MonadFresh (IdentityT m) where
  refreshId = lift . refreshId

instance MonadFresh m => MonadFresh (ExceptT e m) where
  refreshId = lift . refreshId

instance MonadFresh m => MonadFresh (StateT s m) where
  refreshId = lift . refreshId

instance MonadFresh m => MonadFresh (ReaderT r m) where
  refreshId = lift . refreshId

instance MonadFresh m => MonadFresh (ContT r m) where
  refreshId = lift . refreshId

-------------------------------------------------------------------------------
-- Mist AST instances ---------------------------------------------------------
-------------------------------------------------------------------------------

instance Bifunctor Expr where
  second = fmap
  first f (AnnNumber i ann l) = AnnNumber i (f ann) l
  first f (AnnBoolean b ann l) = AnnBoolean b (f ann) l
  first f (AnnUnit ann l) = AnnUnit (f ann) l
  first f (AnnId x ann l) = AnnId x (f ann) l
  first f (AnnPrim op ann l) = AnnPrim op (f ann) l
  first f (AnnIf e1 e2 e3 ann l) = AnnIf (first f e1) (first f e2) (first f e3) (f ann) l
  first f (AnnLet bind e1 e2 ann l) = AnnLet (first f bind) (first f e1) (first f e2) (f ann) l
  first f (AnnApp e1 e2 ann l) = AnnApp (first f e1) (first f e2) (f ann) l
  first f (AnnLam bind e ann l) = AnnLam (first f bind) (first f e) (f ann) l
  first f (AnnTApp e t ann l) = AnnTApp (first f e) t (f ann) l
  first f (AnnTAbs alpha e ann l) = AnnTAbs alpha (first f e) (f ann) l

instance Bifunctor Bind where
  second = fmap
  first f a@AnnBind{bindAnn = ann} = a{bindAnn = f ann}

instance Bifunctor ParsedAnnotation where
  second = fmap
  first f (ParsedCheck r) = ParsedCheck $ first f r
  first f (ParsedAssume r) = ParsedAssume $ first f r
  first _ ParsedInfer = ParsedInfer

instance Bifunctor ElaboratedAnnotation where
  second = fmap
  first f (ElabRefined r) = ElabRefined $ first f r
  first f (ElabAssume r) = ElabAssume $ first f r
  first _ (ElabUnrefined typ) = ElabUnrefined typ

instance Bifunctor RType where
  second = fmap
  first f (RBase b t r) = RBase b t (f r)
  first f (RApp c ts) = RApp c $ (\(a, b) -> (a, first f b)) <$> ts
  first f (RFun b rt1 rt2) = RFun b (first f rt1) (first f rt2)
  first f (RIFun b rt1 rt2) = RIFun b (first f rt1) (first f rt2)
  first f (RRTy b rt r) = RRTy b (first f rt) (f r)
  first f (RForall tvar rt) = RForall tvar (first f rt)
  first f (RForallP tvar rt) = RForallP tvar (first f rt)

class Default a where
  defaultVal :: a

instance Default () where
  defaultVal = ()

instance Default (Maybe a) where
  defaultVal = Nothing
