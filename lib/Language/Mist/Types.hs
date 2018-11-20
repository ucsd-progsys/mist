{-# LANGUAGE DeriveFunctor        #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances    #-}

module Language.Mist.Types
  (
  -- * Re-Export SourceSpans
    module Language.Mist.UX

  -- * Aliases for various identifiers
  , Id
  , Tag

  -- * Types and Polys
  , Sig (..), Type (..), Poly (..), TVar (..), Ctor (..)

  -- * Abstract syntax of the Adder language
  , Field (..)
  , Bind  (..)
  , Expr  (..)
  , Def 
  , AnfExpr,   ImmExpr
  , BareBind, Bare, BareDef
  , Prim2 (..)
  , isAnf

  -- * Smart Constructors
  , bindsExpr
  , defsExpr 
  -- , dec

  -- * Destructors
  , exprDefs 

  -- * Labels
  , label
  , getLabel

    -- * Environments
  , Env
  , emptyEnv
  , pushEnv
  , lookupEnv
  , memberEnv
  , addEnv
  , fromListEnv
  , envMax
  -- , insertEnv

  -- * Abstract Text Type
  , Ext (..)
  , ext

  
  ) where

import           GHC.Exts( IsString(..) )
import           Prelude
import qualified Data.List        as L
import           Data.Maybe                       (isJust)
import           Text.Printf
import qualified Text.PrettyPrint  as PP
import           System.FilePath                  ((<.>))
import           Language.Mist.UX

-- type Nat      = Int

--------------------------------------------------------------------------------
-- | Abstract syntax of Mist
--------------------------------------------------------------------------------

-- | `Id` are program variables
type Id = Text

-- | `Tag` are used to tag each `If`
type Tag = Int

-- | `Prim2` are binary operations
data Prim2
  = Plus
  | Minus
  | Times
  | Less
  | Greater
  | Equal
  deriving (Show)

-- | Expr are single expressions
data Expr a
  = Number  !Integer                       a
  | Boolean !Bool                          a
  | Id      !Id                            a
  | Prim2   !Prim2    !(Expr a)  !(Expr a) a
  | If      !(Expr a) !(Expr a)  !(Expr a) a
  | Let     !(Bind a) !Sig       !(Expr a)  !(Expr a) a
  | Tuple   !(Expr a) !(Expr a)            a
  | GetItem !(Expr a) !Field               a
  | App     !(Expr a) !(Expr a)            a
  | Lam               [Bind a]   !(Expr a) a
  | Unit                                   a
    deriving (Show, Functor)

data Sig
  = Infer
  | Check  Poly
  | Assume Poly
    deriving (Show)

data Field
  = Zero
  | One
    deriving (Show)

data Bind a = Bind
  { bindId    :: !Id
  , bindLabel :: a
  }
  deriving (Show, Functor)

type Def a = (Bind a, Sig, Expr a)


-- | Constructing a function declaration
-- dec :: Bind a -> Sig -> [Bind a] -> Expr a -> Expr a -> a -> Expr a
-- dec f t xs e e' l = Let f (Fun f t xs e l) e' l

defsExpr :: [Def a] -> Expr a 
defsExpr bs@((b,_,_):_)   = go (bindLabel b) bs  
  where 
    go l []               = Unit l
    go _ ((b, s, e) : ds) = Let b s e (go l ds) l where l = bindLabel b

-- | Constructing `Expr` from let-binds
bindsExpr :: [(Bind a, Expr a)] -> Expr a -> a -> Expr a
bindsExpr bs e l = foldr (\(x, e1) e2  -> Let x Infer e1 e2 l) e bs

-- | Destructing `Expr` into let-binds
exprDefs :: Expr a -> ([Def a], Expr a)
exprDefs = go 
  where 
    go (Let x s e e' _) = ((x, s, e) : bs, body) where  (bs, body) = go e'
    go body             = ([]            , body)

--------------------------------------------------------------------------------
getLabel :: Expr a -> a
--------------------------------------------------------------------------------
getLabel (Number _ l)    = l
getLabel (Boolean _ l)   = l
getLabel (Id _ l)        = l
getLabel (Prim2 _ _ _ l) = l
getLabel (If    _ _ _ l) = l
getLabel (Let _ _ _ _ l) = l
getLabel (App _ _ l)     = l
getLabel (Tuple _ _ l)   = l
getLabel (GetItem _ _ l) = l
getLabel (Lam _ _ l)     = l
-- getLabel (Fun _ _ _ _ l) = l
getLabel (Unit  l)       = l 

--------------------------------------------------------------------------------
-- | Dynamic Errors
--------------------------------------------------------------------------------

-- | DynError correspond to different kind of dynamic/run-time errors
data DynError
  = TypeError Ty
  | ArithOverflow
  | IndexLow
  | IndexHigh
  | ArityError
  deriving (Show)

-- | Ty correspond to two kinds of values
data Ty
  = TNumber
  | TBoolean
  | TTuple
  | TClosure
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

ppSig k b _s = printf "%s %s %s\n" (pprint b) k "TODO-SIGNATURE" -- (pprint s) 
ppEqn b e    = printf "%s = \n" (pprint b)
            ++ nest 2           (pprint e)

nest       :: Int -> Text -> Text
nest n     = unlines . map pad . lines
  where
    pad s  = blanks ++ s
    blanks = replicate n ' '


--------------------------------------------------------------------------------
-- | Transformation to ensure each sub-expression gets a distinct tag
--------------------------------------------------------------------------------
label :: Expr a -> Expr (a, Tag)
--------------------------------------------------------------------------------
label = snd . go 0
  where
    go i (Unit l)          = labelTop i l  Unit 

    go i (Number n l)      = labelTop i  l (Number n)

    go i (Boolean b l)     = labelTop i  l (Boolean b)

    go i (Id     x l)      = labelTop i  l (Id x)

    go i (Prim2 o e1 e2 l) = labelTop i'' l (Prim2 o e1' e2')
      where
        (i',  e1')         = go i  e1
        (i'', e2')         = go i' e2

    go i (If c e1 e2 l)    = labelTop i''' l (If c' e1' e2')
      where
        (i'  , c' )        = go i   c
        (i'' , e1')        = go i'  e1
        (i''', e2')        = go i'' e2

    go i (Let x s e b l)   = labelTop i'' l (Let x' s e' b')
      where
        (i', [e', b'])     = L.mapAccumL go i [e, b]
        (i'', x')          = labelBind i' x

    go i (Tuple e1 e2 l)   = labelTop i' l (Tuple e1' e2')
      where
        (i', [e1', e2'])   = L.mapAccumL go i [e1, e2]

    go i (GetItem e1 f l) = labelTop i' l (GetItem e1' f)
      where
        (i', e1')          = go i e1

    go i (Lam xs e l)      = labelTop i'' l (Lam xs' e')
      where
        (i', e')           = go i e
        (i'', xs')         = L.mapAccumL labelBind i' xs

    -- go i (Fun f t xs e l)  = labelTop i'' l (Fun f' t xs' e')
      -- where
        -- (i', e')           = go i e
        -- (i'', f':xs')      = L.mapAccumL labelBind i' (f:xs)

    go i (App e1 e2 l)     = labelTop i' l (App e1' e2')
      where
        (i', [e1', e2'])   = L.mapAccumL go i [e1, e2]

labelTop :: Tag -> a -> ((a, Tag) -> b) -> (Tag, b)
labelTop i l c             = (i + 1, c (l, i))

labelBind :: Tag -> Bind a -> (Tag, Bind (a, Tag))
labelBind i (Bind x l)     = labelTop i l (Bind x)

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
--isAnf (Fun _ _ _ e _)  = isAnf e

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

--------------------------------------------------------------------------------
-- | The `Bare` types are for parsed ASTs.
--------------------------------------------------------------------------------

type Bare     = Expr SourceSpan
type BareBind = Bind SourceSpan
type BareDef  = Def  SourceSpan 

instance Located Bare where
  sourceSpan = getLabel

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
data Type =  TVar TVar          -- a
          |  TInt               -- Int
          |  TBool              -- Bool
          |  [Type] :=> Type    -- (t1,...,tn) => t2
          |  TPair Type Type    -- (t0, t1)
          |  TCtor Ctor [Type]  -- Ctor [t1,...,tn]
          deriving (Eq, Ord)

newtype Ctor = CT String deriving (Eq, Ord)

newtype TVar = TV String deriving (Eq, Ord)

data Poly  =  Forall [TVar] Type       -- forall a. a -> a -> Bool

instance Show Ctor where
  showsPrec _ c = shows (prCtor c)

instance Show TVar where
  showsPrec _ x = shows (prTVar x)

instance Show Type where
  showsPrec _ x = shows (prType x)

instance Show Poly where
  showsPrec _ x = shows (prPoly x)

instance IsString TVar where
  fromString = TV

instance IsString Type where
  fromString = TVar . TV

instance PPrint Type where 
  pprint = show 

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

--------------------------------------------------------------------------------
-- | File Extensions
--------------------------------------------------------------------------------

data Ext = Src    -- ^ source
         | Asm    -- ^ ascii  assembly
         | Exe    -- ^ x86    binary
         | Res    -- ^ output of execution
         | Log    -- ^ compile and execution log

instance Show Ext where
  show Src = "gtr"
  show Asm = "s"
  show Exe = "run"
  show Res = "result"
  show Log = "log"

ext :: FilePath -> Ext -> FilePath
ext f e = f <.> show e
