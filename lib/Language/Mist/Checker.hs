{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE TupleSections              #-}
{-# LANGUAGE TypeSynonymInstances       #-}
{-# LANGUAGE NoMonomorphismRestriction  #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE PatternSynonyms            #-}

--------------------------------------------------------------------------------
-- | This module contains the code for type check an `Expr`
-- and elaborating it to a `Core`.
--
-- The algorithm is based on "Complete and Easy Bidirectional Typechecking
-- for Higher-Rank Polymorphism" by Dunfield and Krishnaswami
--------------------------------------------------------------------------------
module Language.Mist.Checker
  ( -- * Top-level Static Checker
    wellFormed
  , typeCheck

    -- * type check and produce an elaborated expression
  , elaborate

    -- * Error Constructors
  , errUnboundVar
  , errUnboundFun

  , prim2Unpoly
  ) where


import           Data.Maybe (fromMaybe)
import qualified Data.Map          as M
import qualified Data.Set          as S
import qualified Data.List         as L
import qualified Control.Exception as Ex
import           Text.Printf (printf)
import           Control.Monad.State
import           Control.Monad.Except
import           Data.Foldable (fold)

import           Language.Mist.Types
import           Language.Mist.Utils
import           Language.Mist.Names


--------------------------------------------------------------------------------
-- | `wellFormed e` returns the list of errors for an expression `e`
--------------------------------------------------------------------------------
wellFormed :: Bare -> [UserError]
wellFormed = go emptyEnv
  where
    gos                       = concatMap . go
    go _    (Unit    {})      = []
    go _    (Boolean {})      = []
    go _    (Number  n     l) = largeNumberErrors n l
    go vEnv (Id      x     l) = unboundVarErrors vEnv x l
    go vEnv (Prim2 _ e1 e2 _) = gos vEnv [e1, e2]
    go vEnv (If   e1 e2 e3 _) = gos vEnv [e1, e2, e3]
    go vEnv (Let x _ e1 e2 _) = duplicateBindErrors vEnv x
                                ++ go vEnv e1
                                ++ go (addEnv x vEnv) e2
    go vEnv (Tuple e1 e2   _) = gos vEnv [e1, e2]
    go vEnv (GetItem e1 _ _)  = go  vEnv e1
    go vEnv (App e1 e2     _) = gos vEnv [e1, e2]
    go vEnv (Lam x e      _)  = go (addEnv x vEnv) e

--------------------------------------------------------------------------------
-- | Error Checkers: In each case, return an empty list if no errors.
--------------------------------------------------------------------------------
duplicateBindErrors :: Env -> BareBind -> [UserError]
duplicateBindErrors vEnv x
  = condError (memberEnv (bindId x) vEnv) (errDupBind x)

largeNumberErrors :: Integer -> SourceSpan -> [UserError]
largeNumberErrors n l
  = condError (maxInt < abs n) (errLargeNum l n)

maxInt :: Integer
maxInt = 1073741824

unboundVarErrors :: Env -> Id -> SourceSpan -> [UserError]
unboundVarErrors vEnv x l
  = condError (not (memberEnv x vEnv)) (errUnboundVar l x)

--------------------------------------------------------------------------------
-- | Error Constructors
--------------------------------------------------------------------------------

condError :: Bool -> UserError -> [UserError]
condError True  e = [e]
condError False _ = []

errDupBind      x  = mkError (printf "Shadow binding '%s'" (bindId x))      (sourceSpan x)
errLargeNum   l n  = mkError (printf "Number '%d' is too large" n) l
errUnboundVar l x  = mkError (printf "Unbound variable '%s'" x) l
errUnboundFun l f  = mkError (printf "Function '%s' is not defined" f) l
errUnify l t1 t2   = mkError (printf "Type error: cannot unify %s and %s" (show t1) (show t2)) l
errMismatch l s s' = mkError (printf "Type error: mismatched function signature: specified %s but inferred %s" (show s) (show s')) l
errOccurs l a t    = mkError (printf "Type error: occurs check fails: %s occurs in %s" (show a) (show t)) l

--------------------------------------------------------------------------------
typeCheck :: (Located a) => Expr a -> Type
--------------------------------------------------------------------------------
typeCheck = typeInfer env0
  where
    env0  = OldTypeEnv M.empty

_showType :: Expr a -> Type -> IO ()
_showType e t = putStrLn $ pprint e ++ " :: " ++ show t

-------------------------------------------------------------------------------- typeInfer :: (Located a) => OldTypeEnv -> Expr a -> Type
--------------------------------------------------------------------------------
typeInfer env e = apply su t
  where
    (su, t)     = ti env empSubst e

--------------------------------------------------------------------------------
ti :: (Located a) => OldTypeEnv -> OldSubst -> Expr a -> (OldSubst, Type)
--------------------------------------------------------------------------------
ti _ su   (Number {})      = (su, TInt)

ti _ su   (Boolean {})     = (su, TBool)

ti env su e@(Id x l)       = traceShow False (pprint e) $ instantiate su (lookupOldTypeEnv (sourceSpan l) x env)

-- the following cases reduce to special "function applications", handled by instApp
ti env su (If e1 e2 e3 l)  = instApp (sourceSpan l) env su ifPoly [e1, e2, e3]

ti env su (Prim2 p e e' l) = instApp (sourceSpan l) env su (prim2Poly p) [e,e']

ti env su (Tuple e e' l)   = instApp (sourceSpan l) env su tupPoly [e, e']

ti env su (GetItem e f l)  = instApp (sourceSpan l) env su (fieldPoly f) [e]

-- Trusted signature: just add x := s to the env and use it to check `e`
ti env su (Let x (Assume s) _ e _)
                           = traceShow False (pprint x) $ ti env' su e
  where
    env'                   = extOldTypeEnv (bindId x) (eraseRType s) env

ti env su (App eF eArg l)  = tiApp (sourceSpan l) sF (apply sF env) tF [eArg]
  where
    (sF, tF)               = ti env su eF                            -- eF :: T1

-- HIDE?
{- actual
ti env su (Lam xs e l)     = tiFun sp env xs e su' Nothing tXs tOut
  where
    (su', tXs :=> tOut)    = freshFun su (length xs)
    sp                     = sourceSpan l
-}

{- starter -}
ti env su (Lam x body l)   = (su3, apply su3 (tX :=> tOut))
  where
    (su1, tX :=> tOut)     = freshFun su
    env'                   = extTypesEnv env [(x, tX)]
    (su2, tBody)           = ti env' su1 body
    su3                    = unify sp su2 tBody (apply su2 tOut)
    sp                     = sourceSpan l

-- OLD-FUN ti env su (Fun f Infer xs e _)
                           -- OLD-FUN = tiFun sp env xs e su' (Just f) tXs tOut
  -- OLD-FUN where
    -- OLD-FUN (su', tXs :=> tOut)    = freshFun su (length xs)
    -- OLD-FUN sp                     = sourceSpan (bindLabel f)

-- HIDE : HARD
ti env su (Let f (Check rs1) e1 e2 _)
  | ok                     = ti env' su'' e2
  | otherwise              = abort (errMismatch sp s1 s1')
  where
    ok                     = eqPoly s1 s1'
    s1'                    = generalize env (apply su'' t1')
    (su'', t1')            = ti env' su' e1
    env'                   = extOldTypeEnv (bindId f) s1 env
    (su' , _t)             = instantiate su s1
    sp                     = sourceSpan (bindLabel f)
    s1                     = eraseRType rs1

-- ti env su (Fun f (Check s) xs e _)
--   | ok                     = (su'', t')
--   | otherwise              = abort (errMismatch sp s s')
  -- where
    -- ok                     = eqPoly (generalize env t) (generalize env t')
    -- s'                     = generalize env t'
    -- (su'', t')             = tiFun sp env xs e su' (Just f) tXs tOut
    -- (su' , t)              = instantiate su s
    -- (tXs, tOut)            = splitFun sp (length xs) t
    -- sp                     = sourceSpan (bindLabel f)

ti env su e@(Let x _ e1 e2 _) = traceShow False (pprint e) $ ti env'' su1 e2                         -- e2 :: T2
  where
    env''                  = extOldTypeEnv (bindId x) s1 env'
    (su1, t1)              = ti env su e1                            -- e1 :: T1
    env'                   = apply su1 env
    s1                     = generalize env' t1

-- DEAD CODE
ti _ su (Unit _)           = (su, TInt) -- panic "ti: dead code" (sourceSpan (extract e))

freshFun :: OldSubst -> (OldSubst, Type)
freshFun su = (su', tX :=> tOut)
  where
    (su' , [tOut, tX]) = freshTVars su 2

eqPoly  :: Type -> Type -> Bool
eqPoly (TForall a s) (TForall b t) = apply su s == t
  where
    su                     = mkSubst [(a, TVar b)]
eqPoly s t = s == t

extTypesEnv :: OldTypeEnv -> [(Bind a, Type)] -> OldTypeEnv
extTypesEnv = foldr (\(x, t) -> extOldTypeEnv (bindId x) t)

-----------------------------------------------------------------------------------------------
instApp :: (Located a) => SourceSpan -> OldTypeEnv -> OldSubst -> Type -> [Expr a] -> (OldSubst, Type)
-----------------------------------------------------------------------------------------------
instApp sp env su sF       = tiApp sp su' env tF
  where
    (su', tF)              = instantiate su sF

-----------------------------------------------------------------------------------------------
tiApp :: (Located a) => SourceSpan -> OldSubst -> OldTypeEnv -> Type -> [Expr a] -> (OldSubst, Type)
-----------------------------------------------------------------------------------------------
tiApp sp su env tF eIns   = (su''', apply su''' tOut)
  where
    (su' , tIns)          = L.mapAccumL (ti env) su eIns
    (su'', tOut)          = freshTVar su'
    su'''                 = unify sp su'' tF (foldr (:=>) tOut tIns)

-- HIDE
tupPoly, ifPoly :: Type
tupPoly  = TForall "a" (TForall "b" ("a" :=> ("b" :=> TPair "a" "b")))
ifPoly   = TForall "a" (TBool :=>  ("a" :=> ("a" :=> "a")))

-- HIDE
fieldPoly :: Field -> Type
fieldPoly Zero = TForall "a" (TForall "b" (TPair "a" "b" :=> "a"))
fieldPoly One  = TForall "a" (TForall "b" (TPair "a" "b" :=> "b"))

-- HIDE
prim2Poly :: Prim2 -> Type
prim2Poly Plus    = TInt :=> (TInt :=> TInt)
prim2Poly Minus   = TInt :=> (TInt :=> TInt)
prim2Poly Times   = TInt :=> (TInt :=> TInt)
prim2Poly Less    = TInt :=> (TInt :=> TBool)
prim2Poly Greater = TInt :=> (TInt :=> TBool)
prim2Poly And     = TBool :=> (TBool :=> TBool)
prim2Poly Equal   = TForall "a" ("a" :=> ("a" :=> TBool))

prim2Unpoly c = go $ prim2Poly c
  where
    go (TForall _ t) = go t
    go (_ :=> (_ :=> t)) = t
    go _ = error "prim2Poly on a prim which is not a binary function"

--------------------------------------------------------------------------------
unify :: SourceSpan -> OldSubst -> Type -> Type -> OldSubst
--------------------------------------------------------------------------------
unify sp su (l :=> r) (l' :=> r') = s2
  where
    s1                                = unify sp su l l'
    s2                                = unify sp s1 (apply s1 r) (apply s1 r')

-- HIDE
unify sp su (TCtor c ts) (TCtor c' ts')
  |  c == c'
  && length ts == length ts'          = unifys sp su ts ts'

-- HIDE
unify sp su (TPair s1 s2) (TPair t1 t2) = unifys sp su [s1, s2] [t1, t2]

unify sp su (TVar a) t                  = varAsgn sp su a t
unify sp su t (TVar a)                  = varAsgn sp su a t
unify _ su TInt TInt                    = su
unify _ su TBool TBool                  = su
unify sp _  t1 t2                       = abort (errUnify sp t1 t2)

-- | `unifys` recursively calls `unify` on *lists* of types:
unifys :: SourceSpan -> OldSubst -> [Type] -> [Type] -> OldSubst
unifys sp su (t:ts) (t':ts') = unifys sp su' (apply su' ts) (apply su' ts')
  where
    su'                      = unify sp su t t'
unifys _  su []     []       = su
unifys sp _  _      _        = panic "unifys: dead code" sp

_unify sp env su t1 t2 = traceShow False ("MGU: env = " ++ show env ++ " t1 = " ++ show t1 ++ ", t2 = " ++ show t2) su'
  where
    su'           = unify sp su t1 t2

--------------------------------------------------------------------------------
-- | `varAsgn su a t` extends `su` with `[a := t]` if **required** and **possible**!
varAsgn :: SourceSpan -> OldSubst -> TVar -> Type -> OldSubst
--------------------------------------------------------------------------------
varAsgn sp su a t
  | t == TVar a          =  su
  | a `elem` freeTvars t =  abort (errOccurs sp a t)
  | otherwise            =  extSubst su a t

--------------------------------------------------------------------------------
generalize :: OldTypeEnv -> Type -> Type
--------------------------------------------------------------------------------
generalize env t = (foldr TForall t as)
  where
    as           = L.nub (tvs L.\\ evs)
    tvs          = freeTvars t
    evs          = freeTvars env

--------------------------------------------------------------------------------
instantiate :: OldSubst -> Type -> (OldSubst, Type)
--------------------------------------------------------------------------------
instantiate su (TForall a t) = (su', apply suInst t)
  where
    (su', a')                = freshTVar su
    suInst                   = mkSubst [(a, a')]
instantiate su t = (su, t)

--------------------------------------------------------------------------------
-- | Environments --------------------------------------------------------------
--------------------------------------------------------------------------------

newtype OldTypeEnv = OldTypeEnv (M.Map Id Type)

extOldTypeEnv :: Id -> Type -> OldTypeEnv -> OldTypeEnv
extOldTypeEnv x s (OldTypeEnv env) =  OldTypeEnv $ M.insert x s env
  where
    -- _env  = traceShow _msg _env
    -- _msg  = "extOldTypeEnv: " ++ show x ++ " := " ++ show s

lookupOldTypeEnv :: SourceSpan -> Id -> OldTypeEnv -> Type
lookupOldTypeEnv l x (OldTypeEnv env) = fromMaybe err  (M.lookup x env)
  where
    err                         = abort (errUnboundVar l x)

--------------------------------------------------------------------------------
-- | Substitutions -------------------------------------------------------------
--------------------------------------------------------------------------------
data OldSubst   = Su { suMap :: M.Map TVar Type
                  , suCnt :: !Int
                  }

empSubst :: OldSubst
empSubst =  Su M.empty 0

extSubst :: OldSubst -> TVar -> Type -> OldSubst
extSubst su a t = su { suMap = M.insert a t su' }
  where
     su'        = apply (mkSubst [(a, t)]) (suMap su)


mkSubst :: [(TVar, Type)] -> OldSubst
mkSubst ats = Su (M.fromList ats) 666

unSubst :: [TVar] -> OldSubst -> OldSubst
unSubst as su = su { suMap = foldr M.delete (suMap su) as }

freshTVars :: OldSubst -> Int -> (OldSubst, [Type])
freshTVars su n = L.mapAccumL (\a _ -> freshTVar a) su (replicate n ())

freshTVar :: OldSubst -> (OldSubst, Type)
freshTVar su = (su', TVar (TV ("a" ++ show i)))
  where
    (su', i) = fresh su

fresh :: OldSubst -> (OldSubst, Int)
fresh su  = (su {suCnt = n + 1}, n) where n = suCnt su

--------------------------------------------------------------------------------
-- Applying Substitutions ------------------------------------------------------
--------------------------------------------------------------------------------

class Substitutable a where
  apply     :: OldSubst -> a -> a
  freeTvars :: a -> [TVar]

instance Substitutable Type where
  apply _  TInt            = TInt
  apply _  TBool           = TBool
  apply su t@(TVar a)      = M.findWithDefault t a (suMap su)
  apply su (ts :=> t)      = apply su ts :=> apply su t
  apply su (TPair t1 t2)   = TPair (apply su t1) (apply su t2)
  apply su (TCtor c ts)    = TCtor c (apply su ts)
  apply _ TUnit            = TUnit
  apply s (TForall a t)    = TForall a $ apply (unSubst [a] s)  t

  freeTvars TInt           = []
  freeTvars TBool          = []
  freeTvars TUnit          = []
  freeTvars (TVar a)       = [a]
  freeTvars (ts :=> t)     = freeTvars ts ++ freeTvars t
  freeTvars (TPair t1 t2)  = freeTvars t1 ++ freeTvars t2
  freeTvars (TCtor _ ts)   = freeTvars ts
  freeTvars (TForall a t)  = freeTvars t L.\\ [a]

instance (Functor t, Foldable t, Substitutable a) => Substitutable (t a) where
  apply     = fmap . apply
  freeTvars = foldr (\x r -> freeTvars x ++ r) []

instance Substitutable OldTypeEnv where
  apply s   (OldTypeEnv env) =  OldTypeEnv   (apply s <$> env)
  freeTvars (OldTypeEnv env) =  freeTvars (M.elems     env)

--------------------------------------------------------------------------------
-- Printing Types --------------------------------------------------------------
--------------------------------------------------------------------------------

instance Show OldSubst where
  show (Su m n) = show (m, n)

instance Show OldTypeEnv where
  showsPrec x (OldTypeEnv m) = showsPrec x (M.toList m)

instance Ex.Exception String where


--------------------------------------------------------------------------------
-- Context -----------------------------------------------------------------
--------------------------------------------------------------------------------

type EVar = TVar

pattern EVar :: TVar -> Type
pattern EVar var = TVar var

data TypeEnvPart
  = Scope EVar       -- ^ Maintains the starting scope of an existential variable
  | Unsolved EVar    -- ^ An unsolved existential variable
  | Solved EVar Type -- ^ A solved existential variable. These variables can only be instantiated to monotypes
  | VarBind Id Type  -- ^ The type bound to a term variable
  | BoundTVar TVar   -- ^ Asserts that the type variable is bound in the context
  deriving (Eq)

-- DEBUGGING
instance Show TypeEnvPart where
  show (Scope evar) = ">" ++ pprint evar
  show (Unsolved evar) = pprint evar
  show (Solved evar typ) = pprint evar ++ "=" ++ pprint typ
  show (VarBind id typ) = show id ++ ":" ++ pprint typ
  show (BoundTVar tvar) = "$" ++ pprint tvar

-- | Ordered typing environment. Grows to the right.
-- Bindings can only depend on things to the left of themselves.
newtype TypeEnv = TypeEnv [TypeEnvPart]
  deriving (Show)

data Ctxt = Ctxt { typeEnv :: TypeEnv
                 , existentials :: S.Set TVar -- ^ The set of existential variables
                 }

type Context tag = StateT Ctxt (FreshT (TypingEither tag))
-- DEBUGGING
-- type Context tag = StateT Ctxt (FreshT (StateT String (TypingEither tag)))

-- DEBUGGING
-- tell :: String -> Context tag ()
-- tell str = lift . lift . modify $ (\stuff -> stuff ++ str ++ "\n")

-- DEBUGGING
-- untell :: Context tag String
-- untell = lift get

initialCtxt :: Ctxt
initialCtxt = Ctxt { typeEnv = TypeEnv [], existentials = S.empty}

evalContext :: Context tag a -> FreshState -> TypingEither tag a
evalContext m freshState = evalFreshT (evalStateT m initialCtxt) freshState

-- DEBUGGING
-- evalContext m freshState = evalStateT (evalFreshT (evalStateT m initialCtxt) freshState) ""

getBoundType :: Id -> TypeEnv -> Maybe Type
getBoundType id (TypeEnv env) =
    findMap (\case
                VarBind boundId typ -> if boundId == id then Just typ else Nothing
                _ -> Nothing)
    env

applyEnv :: TypeEnv -> Type -> Type
applyEnv env a = subst (envToSubst env) a

-- | Builds a parallel substitution from a TypeEnv
envToSubst :: TypeEnv -> Subst Type
envToSubst (TypeEnv env) =
  foldl (\substitution envPart ->
           case envPart of
             Solved alpha b -> M.insert (unTV alpha) (subst substitution b) substitution
             _ -> substitution)
  M.empty env

getsEnv :: (TypeEnv -> a) -> Context tag a
getsEnv f = gets $ f . typeEnv

getEnv :: Context tag TypeEnv
getEnv = getsEnv id

modifyEnv :: (TypeEnv -> TypeEnv) -> Context tag ()
modifyEnv f = modify $ \ctxt@Ctxt{typeEnv = env} -> ctxt { typeEnv = f env }

setEnv :: TypeEnv -> Context tag ()
setEnv newEnv = modifyEnv $ const newEnv

extendEnv :: [TypeEnvPart] -> TypeEnv -> TypeEnv
extendEnv newParts (TypeEnv env) = TypeEnv $ env `mappend` newParts

-- | Γ, part, Δ -> Γ
dropEnvAfter :: TypeEnvPart -> TypeEnv -> TypeEnv
dropEnvAfter part (TypeEnv env) = TypeEnv $ takeWhile (/= part) env

-- | if Γ[part] = Δ, part, Θ then returns (Δ, Θ)
splitEnvAt :: TypeEnvPart -> TypeEnv -> (TypeEnv, TypeEnv)
splitEnvAt part (TypeEnv env) = (TypeEnv delta, TypeEnv theta)
  where (delta, _:theta) = break (== part) env

-- | Returns True if alpha is to the left of beta in the environment
-- Assumes both are in the environment.
isLeftOf :: EVar -> EVar -> TypeEnv -> Bool
isLeftOf alpha beta (TypeEnv env) = go env
  where
    go [] = error $ printf "environment did not contain %s" (show alpha)
    go (Unsolved evar:env')
      | evar == alpha = True
      | evar == beta  = False
      | otherwise     = go env'
    go (Solved evar _:env')
      | evar == alpha = True
      | evar == beta  = False
      | otherwise     = go env'
    go (_:env') = go env'

generateExistential :: Context tag EVar
generateExistential = do
  newEvar <- TV <$> refreshId "E?"
  modify $ \ctxt@Ctxt{existentials = existSet} -> ctxt { existentials = S.insert newEvar existSet}
  pure newEvar

toEVar :: Type -> Context tag (Maybe EVar)
toEVar (TVar tvar) = do
  isEVar <- gets $ S.member tvar . existentials
  if isEVar then pure $ Just tvar else pure Nothing
toEVar _ = pure Nothing

unsolvedExistentials :: TypeEnv -> [EVar]
unsolvedExistentials (TypeEnv env) = [evar | (Unsolved evar) <- env]

--------------------------------------------------------------------------------
-- Elaboration -----------------------------------------------------------------
--------------------------------------------------------------------------------


-- | Elaborates a surface Expr
-- - adds type annotations
-- - adds explicit type application
-- - adds explicit type abstraction
-- - assumes every name is unique
elaborate :: Expr a -> TypingEither a (Core a)
elaborate e = fst <$> evalContext (synthesize e) emptyFreshState -- TODO: pass around the name state

-- DEBUGGING
-- synthesize e = do
--   env <- getEnv
--   tell $ show env ++ " ⊢ " ++ pprint e ++ " =>"
--   internalsynthesize e

-- TODO: add judgments for documentation
-- | Γ ⊢ e ~> c => A ⊣ Θ
synthesize :: Expr a -> Context a (Core a, Type)
synthesize (Number i tag) = pure (CNumber i tag, TInt)
synthesize (Boolean b tag) = pure (CBoolean b tag, TBool)
synthesize (Unit tag) = pure (CUnit tag, TUnit)
synthesize (Id id tag) = do
  boundType <- getsEnv $ getBoundType id
  case boundType of
    Just typ -> pure (CId id tag, typ)
    Nothing -> throwError $ UnboundIdErr id tag
synthesize (Prim2 operator e1 e2 tag) = do -- TODO: fix this to work for equals and other polymorphic types
  let (typ1 :=> (typ2 :=> typ3)) = primOpType operator
  c1 <- check e1 typ1
  c2 <- check e2 typ2
  pure (CPrim2 operator c1 c2 tag, typ3)
synthesize (If condition e1 e2 tag) = do -- TODO: how to properly handle synthesis of branching
  cCondition <- check condition TBool
  alpha <- generateExistential
  modifyEnv $ extendEnv [Unsolved alpha]
  c1 <- check e1 (EVar alpha)
  env <- getEnv
  let firstBranchType = applyEnv env (EVar alpha)
  c2 <- check e2 firstBranchType
  env' <- getEnv
  pure (CIf cCondition c1 c2 tag, applyEnv env' firstBranchType)
synthesize (Let binding sig e1 e2 tag) =
  typeCheckLet binding sig e1 e2 tag
  (\annBind c1 e2 tag -> do
      (c2, inferredType) <- synthesize e2
      pure (CLet annBind c1 c2 tag, inferredType))
synthesize (Tuple e1 e2 tag) = do
  (c1, t1) <- synthesize e1
  (c2, t2) <- synthesize e2
  pure (CTuple c1 c2 tag, TPair t1 t2)
synthesize (GetItem e field tag) = do
  selectorType <- selectorToType field
  synthesizeApp selectorType (selectorToPrim field tag) e tag
synthesize (App e1 e2 tag) = do
  (c1, funType) <- synthesize e1
  env <- getEnv
  synthesizeApp (applyEnv env funType) c1 e2 tag
synthesize (Lam bind e tag) = do
  alpha <- generateExistential
  beta <- generateExistential
  let newBinding = VarBind (bindId bind) (EVar alpha)
  modifyEnv $ extendEnv [Unsolved alpha, Unsolved beta, newBinding]
  c <- check e (EVar beta)
  modifyEnv $ dropEnvAfter newBinding -- TODO: do we need to do something with delta' for elaboration?
  let annBind = AnnBind { aBindId = bindId bind
                        , aBindType = typeToCoreRType (EVar alpha) (bindLabel bind)
                        , aBindLabel = bindLabel bind
                        }
  pure (CLam annBind c tag, EVar alpha :=> EVar beta)

-- DEBUGGING
-- check e t = do
--   env <- getEnv
--   tell $ show env ++ " ⊢ " ++ pprint e ++ " <= " ++ pprint t
--   internalcheck e t

-- | Γ ⊢ e ~> c <= A ⊣ Θ
check :: Expr a -> Type -> Context a (Core a)
check expr (TForall tvar typ) = do
  modifyEnv $ extendEnv [BoundTVar tvar]
  c <- check expr typ
  modifyEnv $ dropEnvAfter (BoundTVar tvar)
  pure c
check expr typ = do
  maybeEVar <- toEVar typ
  case maybeEVar of
    Just _  -> checkSub expr typ
    Nothing -> go expr typ

  where
    go (Number i tag) TInt = pure $ CNumber i tag
    go (Boolean b tag) TBool = pure $ CBoolean b tag
    go e@Id{} t = checkSub e t
    go e@Prim2{} t = checkSub e t
    go (If condition e1 e2 tag) t = do
      cCondition <- check condition TBool
      c1 <- check e1 t
      c2 <- check e2 t
      pure $ CIf cCondition c1 c2 tag
    go (Let binding sig e1 e2 tag) t =
      typeCheckLet binding sig e1 e2 tag
      (\annBind c1 e2 tag -> do
          c2 <- check e2 t
          pure $ CLet annBind c1 c2 tag)
    go (Tuple e1 e2 tag) (TPair t1 t2) = do
      c1 <- check e1 t1
      c2 <- check e2 t2
      pure $ CTuple c1 c2 tag
    go e@GetItem{} t = checkSub e t
    go e@App{} t = checkSub e t
    go (Lam bind e tag) (t1 :=> t2) = do
      let newBinding = VarBind (bindId bind) t1
      modifyEnv $ extendEnv [newBinding]
      c <- check e t2
      modifyEnv $ dropEnvAfter newBinding
      let annBind = AnnBind { aBindId = bindId bind
                            , aBindType = typeToCoreRType t1 (bindLabel bind)
                            , aBindLabel = bindLabel bind
                            }
      pure $ CLam annBind c tag
    go (Unit tag) TUnit = pure $ CUnit tag
    go _ _ = error "TODO: this is a checking error"

-- DEBUGGING
-- synthesizeSpine funType cFun eArg = do
--   env <- getEnv
--   tell $ show env ++ " ⊢ " ++ pprint funType ++ " • " ++ pprint eArg ++ " >>"
--   internalsynthesizeSpine funType cFun eArg

-- | Γ ⊢ A_c • e ~> (cFun, cArg) >> C ⊣ Θ
synthesizeSpine :: Type -> Core a -> Expr a -> Context a (Core a, Core a, Type)
synthesizeSpine funType cFun eArg = do
  maybeEVar <- toEVar funType
  case maybeEVar of
    Just tvar -> synthesizeSpineExistential tvar
    Nothing   -> go funType

  where
    synthesizeSpineExistential funEVar = do
      alpha1 <- generateExistential
      alpha2 <- generateExistential
      solveExistential funEVar
                            (EVar alpha1 :=> EVar alpha2)
                            [alpha2, alpha1]
      cArg <- check eArg (EVar alpha1)
      pure (cFun, cArg, EVar alpha2)

    go (t1 :=> t2) = do
      cArg <- check eArg t1
      pure (cFun, cArg, t2)
    go (TForall (TV tv) t) = do
      evar <- generateExistential
      modifyEnv $ extendEnv [Unsolved evar]
      let newFunType = subst1 (EVar evar) tv t
      -- TODO: when do we substitute things? In synthesizeApp?
      -- TODO: do we add the KVar now and again later?
      synthesizeSpine newFunType (CTApp cFun (EVar evar) (extractC cFun)) eArg
    go t = throwError $ ApplyNonFunction t


-- | Γ ⊢ A_c <: B ~> c ⊣ Θ
-- When doing a ∀A.B <: C the subtyping check will infer the
-- polymorphic instantiation for c.
instSub :: Core a -> Type -> Type -> Context tag (Core a)
instSub c a@(TForall _ _) b =
  foldr (\typ instantiated -> CTApp instantiated typ (extractC c)) -- TODO: test that this foldr is the correct order
        c <$> go a b

  where
    go (TForall alpha a) b = do
      evar <- generateExistential
      modifyEnv $ extendEnv [Scope evar, Unsolved evar]
      instantiations <- go (subst1 (EVar evar) (unTV alpha) a) b
      (delta, delta') <- getsEnv $ splitEnvAt (Scope evar)
      setEnv delta
      pure (applyEnv delta' (EVar evar):instantiations)
    go a b = do
      a <: b
      pure []

instSub c a b = do
  a <: b
  pure c

-- DEBUGGING
-- a <: b = do
--   env <- getEnv
--   tell $ show env ++ " ⊢ " ++ pprint a ++ " <: " ++ pprint b
--   a <: b

-- | Γ ⊢ A <: B ⊣ Θ
(<:) :: Type -> Type -> Context tag ()
TUnit <: TUnit = pure ()
TInt <: TInt = pure ()
TBool <: TBool = pure ()
a@(TVar _) <: b@(TVar _) | a == b = pure ()
(a1 :=> a2) <: (b1 :=> b2) = do
  b1 <: a1
  env <- getEnv
  (applyEnv env a2) <: (applyEnv env b2)
(TPair a1 a2) <: (TPair b1 b2) = do
  a1 <: b1
  env <- getEnv
  (applyEnv env a2) <: (applyEnv env b2)
(TCtor ctor1 as) <: (TCtor ctor2 bs)
  | ctor1 /= ctor2 = error "TODO: constructor mismatch"
  | otherwise =
    if length as /= length bs
      then error "TODO: constructor application length mismatch"
      else mapM_ (\(a, b) -> do
                    env <- getEnv
                    (applyEnv env a) <: (applyEnv env b))
                  (zip as bs)
(TForall alpha a) <: b = do
  evar <- generateExistential
  modifyEnv $ extendEnv [Scope evar, Unsolved evar]
  (subst1 (EVar evar) (unTV alpha) a) <: b
  modifyEnv $ dropEnvAfter (Scope evar)
a <: (TForall alpha b) = do
  modifyEnv $ extendEnv [BoundTVar alpha]
  a <: b
  modifyEnv $ dropEnvAfter (BoundTVar alpha)
a <: b = do
  maybeAEVar <- toEVar a
  maybeBEVar <- toEVar b
  case (maybeAEVar, maybeBEVar) of
    (Just alpha, Just beta) -> do
      alphaToLeft <- getsEnv $ alpha `isLeftOf` beta
      if alphaToLeft
        then instantiateL alpha (EVar beta)
        else instantiateR (EVar alpha) beta
    (Just evar, _) -> do
      occurrenceCheck evar b
      instantiateL evar b
    (_, Just evar) -> do
      occurrenceCheck evar a
      instantiateR a evar
    (_, _) -> error "TODO: this is a subtyping error"

-- DEBUGGING
-- instantiateL a b = do
--   env <- getEnv
--   tell $ show env ++ " ⊢ " ++ pprint a ++ " <=: " ++ pprint b
--   internalinstantiateL a b

-- TODO: figure out why we reverse the newly created existentials
instantiateL :: EVar -> Type -> Context tag ()
instantiateL alpha typ = do
  maybeExists <- toEVar typ
  case maybeExists of
    Just beta -> do
      alpha `assertLeftOf` beta
      solveExistential beta (EVar alpha) []
    Nothing -> go typ

  where
    go (a :=> b) = do
      alpha1 <- generateExistential
      alpha2 <- generateExistential
      solveExistential alpha (EVar alpha1 :=> EVar alpha2) [alpha2, alpha1]
      instantiateR a alpha1
      env <- getEnv
      instantiateL alpha2 (applyEnv env b)
    go (TPair a b) = do
      alpha1 <- generateExistential
      alpha2 <- generateExistential
      solveExistential alpha (TPair (EVar alpha1) (EVar alpha2)) [alpha2, alpha1]
      instantiateL alpha1 a
      env <- getEnv
      instantiateL alpha2 (applyEnv env b)
    go (TCtor ctor as) = do
      betas <- mapM (const generateExistential) as
      solveExistential alpha (TCtor ctor (fmap EVar betas)) (reverse betas)
      mapM_ (\(beta, a) -> do
                env <- getEnv
                instantiateL beta (applyEnv env a))
            (zip betas as)
    go (TForall tvar a) = do
      modifyEnv $ extendEnv [BoundTVar tvar]
      instantiateL alpha a
      modifyEnv $ dropEnvAfter (BoundTVar tvar)
    go typ = solveExistential alpha typ []

-- DEBUGGING
-- instantiateR a b = do
--   env <- getEnv
--   tell $ show env ++ " ⊢ " ++ pprint a ++ " :=> " ++ pprint b
--   internalinstantiateR a b

instantiateR :: Type -> EVar -> Context tag ()
instantiateR typ alpha = do
  maybeExists <- toEVar typ
  case maybeExists of
    Just beta -> do
      alpha `assertLeftOf` beta
      solveExistential beta (EVar alpha) []
    Nothing -> go typ

  where
    go (a :=> b) = do
      alpha1 <- generateExistential
      alpha2 <- generateExistential
      solveExistential alpha (EVar alpha1 :=> EVar alpha2) [alpha2, alpha1]
      instantiateL alpha1 a
      env <- getEnv
      instantiateR (applyEnv env b) alpha2
    go (TPair a b) = do
      alpha1 <- generateExistential
      alpha2 <- generateExistential
      solveExistential alpha (TPair (EVar alpha1) (EVar alpha2)) [alpha2, alpha1]
      instantiateR a alpha1
      env <- getEnv
      instantiateR (applyEnv env b) alpha2
    go (TCtor ctor as) = do
      betas <- mapM (const generateExistential) as
      solveExistential alpha (TCtor ctor (fmap EVar betas)) (reverse betas)
      mapM_ (\(a, beta) -> do
                env <- getEnv
                instantiateR (applyEnv env a) beta)
            (zip as betas)
    go (TForall tvar a) = do
      beta <- generateExistential
      modifyEnv $ extendEnv [Scope beta, Unsolved beta]
      instantiateR (subst1 (EVar beta) (unTV tvar) a) alpha
      modifyEnv $ dropEnvAfter (Scope beta)
    go typ = solveExistential alpha typ []

assertLeftOf :: EVar -> EVar -> Context tag ()
alpha `assertLeftOf` beta = do
  alphaToLeft <- getsEnv $ alpha `isLeftOf` beta
  if alphaToLeft
    then pure ()
    else error (printf "TODO: expected Γ[%0$s][%1$s] but got Γ[%1$s][%2$s]" (show alpha) (show beta))

occurrenceCheck :: EVar -> Type -> Context tag ()
occurrenceCheck alpha typ = do
  evars <- freeEVars typ
  if S.member alpha evars
    then throwError $ InfiniteTypeConstraint alpha typ
    else pure ()

primOpType :: Prim2 -> Type
primOpType Plus    = (TInt :=> (TInt :=> TInt))
primOpType Minus   = (TInt :=> (TInt :=> TInt))
primOpType Times   = (TInt :=> (TInt :=> TInt))
primOpType Less    = (TInt :=> (TInt :=> TBool))
primOpType Greater = (TInt :=> (TInt :=> TBool))
primOpType Equal   = error "TODO: support polymorphic equality"
primOpType And     = (TBool :=> (TBool :=> TBool))

checkSub :: Expr a -> Type -> Context a (Core a)
checkSub e t1 = do
  (c, t2) <- synthesize e
  env <- getEnv
  instSub c (applyEnv env t2) (applyEnv env t1)

-- TODO: reintroduce generalizing for non recursive definitions
typeCheckLet
  :: Bind a
  -> Sig a
  -> Expr a
  -> Expr a
  -> a
  -> (AnnBind a -> Core a -> Expr a -> a -> Context a b)
  -> Context a b
typeCheckLet binding Infer e1 e2 tag handleBody = do
  alpha <- generateExistential
  let evar = EVar alpha
  modifyEnv $ extendEnv [Scope alpha, Unsolved alpha, VarBind (bindId binding) evar]
  c1 <- check e1 evar
  (delta, delta') <- getsEnv $ splitEnvAt (Scope alpha)
  setEnv delta
  -- LET GENERALIZATION (not currently allowed)
  -- (boundType, c1) <- letGeneralize binding evar unsubstitutedC1 delta'
  -- TODO: well-formedness error for non-annotated recursive definitions
  let boundType = applyEnv delta' evar
  let newBinding = VarBind (bindId binding) boundType
  modifyEnv $ extendEnv [newBinding]
  let annBind = AnnBind { aBindId = bindId binding
                        , aBindType = typeToCoreRType boundType (bindLabel binding)
                        , aBindLabel = bindLabel binding
                        }
  result <- handleBody annBind c1 e2 tag
  modifyEnv $ dropEnvAfter newBinding
  pure result
typeCheckLet binding (Check rType) e1 e2 tag handleBody = do
  let typ = eraseRType rType
  let newBinding = VarBind (bindId binding) typ
  modifyEnv $ extendEnv [newBinding]
  unabstractedC1 <- check e1 typ
  let c1 = insertTAbs typ unabstractedC1
  elaboratedRType <- checkRType rType
  let annBind = AnnBind { aBindId = bindId binding
                        , aBindType = elaboratedRType
                        , aBindLabel = bindLabel binding
                        }
  result <- handleBody annBind c1 e2 tag
  modifyEnv $ dropEnvAfter newBinding
  pure result
typeCheckLet binding (Assume rType) e1 e2 tag handleBody = do
  let typ = eraseRType rType
  let newBinding = VarBind (bindId binding) typ
  modifyEnv $ extendEnv [newBinding]
  (c1, _) <- synthesize e1
  elaboratedRType <- checkRType rType
  let annBind = AnnBind { aBindId = bindId binding
                        , aBindType = elaboratedRType
                        , aBindLabel = bindLabel binding
                        }
  result <- handleBody annBind c1 e2 tag
  modifyEnv $ dropEnvAfter newBinding
  pure result

-- | Carries out Hindley-Milner style let generalization on the existential variable.
-- Also substitutes for all existentials that were added as annotations
_letGeneralize :: Bind a -> Type -> Core a -> TypeEnv -> Context a (Type, Core a)
_letGeneralize binding t c env = do
  let preGeneralizedFun = applyEnv env t
  freeExistentials <- freeEVars preGeneralizedFun
  let unsolvedAlphas = filter (`elem` freeExistentials) (unsolvedExistentials env)
  pairedNewTvars <- mapM (\alpha -> do
                             a <- TV <$> refreshId "a" -- TODO: special character for inferred type variables
                             pure (alpha, a))
                    unsolvedAlphas
  let substitution = M.fromList $ fmap (\(alpha, a) -> (unTV alpha, TVar a)) pairedNewTvars
  let generalizedType = if null pairedNewTvars
        then preGeneralizedFun
        else foldr (\(_, a) accType -> TForall a accType) (subst substitution preGeneralizedFun) pairedNewTvars
  let instantiatedFunction = foldl (\accFun (_, a) -> CTApp accFun (TVar a) (bindLabel binding)) -- TODO: fix the tag information
                             (CId (bindId binding) (bindLabel binding)) pairedNewTvars
  pure (generalizedType, subst1 instantiatedFunction (bindId binding) $ subst substitution c)

synthesizeApp :: Type -> Core a -> Expr a -> a -> Context a (Core a, Type)
synthesizeApp tFun cFun eArg tag = do
  (cInstantiatedFun, cArg, resultType) <- synthesizeSpine tFun cFun eArg
  env <- getEnv
  let cApplication = subst (envToSubst env) $ CApp cInstantiatedFun cArg tag
  pure (cApplication, resultType)

selectorToPrim :: Field -> a -> Core a
selectorToPrim Zero tag = CPrim Pi0 tag
selectorToPrim One tag = CPrim Pi1 tag

selectorToType :: Field -> Context a Type
selectorToType Zero = do
  tvar0 <- TV <$> refreshId "a"
  tvar1 <- TV <$> refreshId "b"
  pure $ TForall tvar0 (TForall tvar1 (TPair (TVar tvar0) (TVar tvar1) :=> TVar tvar0))
selectorToType One = do
  tvar0 <- TV <$> refreshId "a"
  tvar1 <- TV <$> refreshId "b"
  pure $ TForall tvar0 (TForall tvar1 (TPair (TVar tvar0) (TVar tvar1) :=> TVar tvar1))

checkRType :: RType Expr a -> Context a (RType Core a)
checkRType (RBase bind typ refinement) = do
  let binding = VarBind (bindId bind) typ
  modifyEnv $ extendEnv [binding]
  cRefinement <- check refinement TBool
  modifyEnv $ dropEnvAfter binding
  pure $ RBase bind typ cRefinement
checkRType (RFun bind rtype1 rtype2) = do
  let binding = VarBind (bindId bind) (eraseRType rtype1)
  modifyEnv $ extendEnv [binding]
  newRType1 <- checkRType rtype1
  newRType2 <- checkRType rtype2
  modifyEnv $ dropEnvAfter binding
  pure $ RFun bind newRType1 newRType2
checkRType (RRTy bind rtype pred) = do
  let binding = VarBind (bindId bind) (eraseRType rtype)
  modifyEnv $ extendEnv [binding]
  cPred <- check pred TBool
  newRType <- checkRType rtype
  modifyEnv $ dropEnvAfter binding
  pure $ RRTy bind newRType cPred
checkRType (RForall tvar rtype) = do
  let binding = BoundTVar tvar
  modifyEnv $ extendEnv [binding]
  newRType <- checkRType rtype
  modifyEnv $ dropEnvAfter binding
  pure $ RForall tvar newRType
checkRType (RUnrefined typ) = pure $ RUnrefined typ

-- | Solves an unsolved existential.
-- If this new solution introduces new existentials
-- these are added immediately before the existential we are solving.
-- Errors if the existential does not exist or has already been solved.
solveExistential :: EVar -> Type -> [EVar] -> Context tag ()
solveExistential evar partialSolution newEvars = do
  (TypeEnv env) <- getEnv
  newEnv <- replaceUnsolved env
  setEnv (TypeEnv newEnv)
  where
    replaceUnsolved [] = error "attempting to articulate nonexistent existential"
    replaceUnsolved (Unsolved evar':parts)
      | evar' == evar = pure $ fmap Unsolved newEvars
                               `mappend` [Solved evar partialSolution]
                               `mappend` parts
    replaceUnsolved (Solved evar' _:_)
      | evar' == evar = throwError SolvingSolvedExistential
    replaceUnsolved (part:parts) = (part:) <$> replaceUnsolved parts

freeEVars :: Type -> Context tag (S.Set EVar)
freeEVars typ = eVars typ
  where
    eVars t@(TVar tvar) = do
      maybeEVar <- toEVar t
      pure $ case maybeEVar of
        Just _  -> S.singleton tvar
        Nothing -> S.empty
    eVars TUnit = pure S.empty
    eVars TInt = pure S.empty
    eVars TBool = pure S.empty
    eVars (t1 :=> t2) = S.union <$> eVars t1 <*> eVars t2
    eVars (TPair t1 t2) = S.union <$> eVars t1 <*> eVars t2
    eVars (TCtor _ ts) = fold <$> mapM eVars ts
    eVars (TForall _ t) = eVars t

insertTAbs :: Type -> Core a -> Core a
insertTAbs (TForall tvar typ) c = CTAbs tvar (insertTAbs typ c) (extractC c)
insertTAbs _ c = c


--------------------------------------------------------------------------------
-- Type checker errors ---------------------------------------------------------
--------------------------------------------------------------------------------

type TypingEither a = Either (TypingError a)

data TypingError a
  = MiscErr
  | UnboundIdErr Id a
  | SolvingSolvedExistential -- TODO: error message
  | ApplyNonFunction Type -- TODO: error message
  | InfiniteTypeConstraint EVar Type -- TODO: error message

instance Show (TypingError a) where
  show MiscErr = "Miscellaneous error"
  show (UnboundIdErr id _) = printf "Unbound id: %s" (show id)
  show SolvingSolvedExistential = printf "TODO: attempting to resolved solved existential variable"
  show (ApplyNonFunction t) = printf "TODO: attempting to use non-function type as a function: %s" (show t)
  show (InfiniteTypeConstraint evar typ) = printf "TODO: infinite type constraint: %s ~ %s" (show evar) (show typ)
