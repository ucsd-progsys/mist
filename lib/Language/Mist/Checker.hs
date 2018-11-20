{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE OverloadedStrings         #-}
{-# LANGUAGE TupleSections             #-}
{-# LANGUAGE TypeSynonymInstances      #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE FlexibleInstances         #-}

--------------------------------------------------------------------------------
-- | This module contains the code for Static Checking an `Expr`
--------------------------------------------------------------------------------
module Language.Mist.Checker
  ( -- * Top-level Static Checker
    wellFormed 
  , typeCheck
    -- * add type annoations
  , ann

    -- * Error Constructors
  , errUnboundVar
  , errUnboundFun
  ) where


import           Data.Maybe (fromMaybe)
import qualified Data.Map          as M
import qualified Data.List         as L
import qualified Control.Exception as Ex
import           Text.Printf        (printf)
import           Language.Mist.Types
import           Language.Mist.Utils
-- import           Debug.Trace (trace)


--------------------------------------------------------------------------------
-- | `wellFormed e` returns the list of errors for an expression `e`
--------------------------------------------------------------------------------
wellFormed :: Bare -> [UserError]
wellFormed = go emptyEnv
  where
    gos                       = concatMap . go
    go _    (Unit {})         = []
    go _    (Boolean {})      = []
    go _    (Number  n     l) = largeNumberErrors      n l
    go vEnv (Id      x     l) = unboundVarErrors  vEnv x l
    go vEnv (Prim2 _ e1 e2 _) = gos vEnv [e1, e2]
    go vEnv (If   e1 e2 e3 _) = gos vEnv [e1, e2, e3]
    go vEnv (Let x _ e1 e2 _) = duplicateBindErrors vEnv x
                             ++ go vEnv e1
                             ++ go (addEnv x vEnv) e2
    go vEnv (Tuple e1 e2   _) = gos vEnv [e1, e2]
    go vEnv (GetItem e1 _ _)  = go  vEnv e1
    go vEnv (App e1 e2     _) = gos vEnv [e1, e2]
    go vEnv (Lam xs e      _) = duplicateParamErrors xs
                             ++ go (addsEnv xs vEnv) e
    -- go vEnv (Fun f _ xs e  _) = duplicateParamErrors xs
    --                          ++ go (addsEnv (f:xs) vEnv) e

addsEnv :: [BareBind] -> Env -> Env
addsEnv xs env = L.foldl' (flip addEnv) env xs

--------------------------------------------------------------------------------
-- | Error Checkers: In each case, return an empty list if no errors.
--------------------------------------------------------------------------------
duplicateParamErrors :: [BareBind] -> [UserError]
duplicateParamErrors xs
  = map (errDupParam . head)
  . dupBy bindId
  $ xs

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

errDupParam     x  = mkError (printf "Duplicate parameter '%s'" (bindId x)) (sourceSpan x)
errDupBind      x  = mkError (printf "Shadow binding '%s'" (bindId x))      (sourceSpan x)
errLargeNum   l n  = mkError (printf "Number '%d' is too large" n) l
errUnboundVar l x  = mkError (printf "Unbound variable '%s'" x) l
errUnboundFun l f  = mkError (printf "Function '%s' is not defined" f) l
errUnify l t1 t2   = mkError (printf "Type error: cannot unify %s and %s" (show t1) (show t2)) l
errSignature l t   = mkError (printf "Type error: malformed function signature %s" (show t)) l
errMismatch l s s' = mkError (printf "Type error: mismatched function signature: specified %s but inferred %s" (show s) (show s')) l
errOccurs l a t    = mkError (printf "Type error: occurs check fails: %s occurs in %s" (show a) (show t)) l


--------------------------------------------------------------------------------
ann :: Expr a -> Core (Poly, a)
--------------------------------------------------------------------------------
ann = undefined

--------------------------------------------------------------------------------
typeCheck :: (Located a) => Expr a -> Type 
--------------------------------------------------------------------------------
typeCheck = typeInfer env0 
  where  
    env0  = TypeEnv M.empty

_showType :: Expr a -> Type -> IO ()
_showType e t = putStrLn $ pprint e ++ " :: " ++ show t

--------------------------------------------------------------------------------
typeInfer :: (Located a) => TypeEnv -> Expr a -> Type
--------------------------------------------------------------------------------
typeInfer env e = apply su t
  where
    (su, t)     = ti env empSubst e

--------------------------------------------------------------------------------
ti :: (Located a) => TypeEnv -> Subst -> Expr a -> (Subst, Type)
--------------------------------------------------------------------------------
ti _ su   (Number {})      = (su, TInt)

ti _ su   (Boolean {})     = (su, TBool)

ti env su e@(Id x l)       = traceShow False (pprint e) $ instantiate su (lookupTypeEnv (sourceSpan l) x env)

-- the following cases reduce to special "function applications", handled by instApp
ti env su (If e1 e2 e3 l)  = instApp (sourceSpan l) env su ifPoly [e1, e2, e3]

ti env su (Prim2 p e e' l) = instApp (sourceSpan l) env su (prim2Poly p) [e,e']

ti env su (Tuple e e' l)   = instApp (sourceSpan l) env su tupPoly [e, e']

ti env su (GetItem e f l)  = instApp (sourceSpan l) env su (fieldPoly f) [e]

-- Trusted signature: just add x := s to the env and use it to check `e`
ti env su (Let x (Assume s) _ e _)
                           = traceShow False (pprint x) $ ti env' su e
  where
    env'                   = extTypeEnv (bindId x) s env

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
ti env su (Lam xs body l)  = (su3, apply su3 (tXs :=> tOut))
  where
    (su1, tXs :=> tOut)    = freshFun su (length xs)
    env'                   = extTypesEnv env (zip xs tXs)
    (su2, tBody)           = ti env' su1 body
    su3                    = unify sp su2 tBody (apply su2 tOut)
    sp                     = sourceSpan l

-- OLD-FUN ti env su (Fun f Infer xs e _)
                           -- OLD-FUN = tiFun sp env xs e su' (Just f) tXs tOut
  -- OLD-FUN where
    -- OLD-FUN (su', tXs :=> tOut)    = freshFun su (length xs)
    -- OLD-FUN sp                     = sourceSpan (bindLabel f)

-- HIDE : HARD
ti env su (Let f (Check s1) e1 e2 _)
  | ok                     = ti env' su'' e2
  | otherwise              = abort (errMismatch sp s1 s1')
  where 
    ok                     = eqPoly s1 s1'
    s1'                    = generalize env (apply su'' t1')
    (su'', t1')            = ti env' su' e1
    env'                   = extTypeEnv (bindId f) s1 env 
    (su' , t)              = instantiate su s1
    sp                     = sourceSpan (bindLabel f)

-- ti env su (Fun f (Check s) xs e _)
  -- | ok                     = (su'', t')
  -- | otherwise              = abort (errMismatch sp s s')
  -- where
    -- ok                     = eqPoly (generalize env t) (generalize env t')
    -- s'                     = generalize env t'
    -- (su'', t')             = tiFun sp env xs e su' (Just f) tXs tOut
    -- (su' , t)              = instantiate su s
    -- (tXs, tOut)            = splitFun sp (length xs) t
    -- sp                     = sourceSpan (bindLabel f)

ti env su e@(Let x _ e1 e2 _) = traceShow False (pprint e) $ ti env'' su1 e2                         -- e2 :: T2
  where
    env''                  = extTypeEnv (bindId x) s1 env'
    (su1, t1)              = ti env su e1                            -- e1 :: T1
    env'                   = apply su1 env
    s1                     = generalize env' t1

-- DEAD CODE
ti _ su (Unit _)           = (su, TInt) -- panic "ti: dead code" (sourceSpan (getLabel e))


splitFun :: SourceSpan -> Int -> Type -> ([Type], Type)
splitFun _ n (tXs :=> tOut)
  | length tXs == n             = (tXs, tOut)
splitFun sp _ t                 = abort (errSignature sp t)

freshFun :: Subst -> Int -> (Subst, Type)
freshFun su arity    = (su', tXs :=> tOut)
  where
    (su' , tOut:tXs) = freshTVars su (1 + arity)

eqPoly  :: Poly -> Poly -> Bool
eqPoly (Forall as s) (Forall bs t)
  | length as == length bs = apply su s == t
  | otherwise              = False
  where
    su                     = mkSubst [(a, TVar b) | (a, b) <- zip as bs]

--------------------------------------------------------------------------------
-- DELETE
--------------------------------------------------------------------------------
tiFun :: (Located a) => SourceSpan
                     -> TypeEnv
                     -> [Bind a] -> Expr a
                     -> Subst -> Maybe (Bind a) -> [Type] -> Type
                     -> (Subst, Type)
--------------------------------------------------------------------------------
tiFun sp env xs e su mF tXs tOut
                           = (su'', apply su'' tF)
  where
    env'                   = extTypesEnv env (funBind mF tF ++ zip xs tXs)
    (su', tBody)           = ti env' su e
    su''                   = unify sp su' tBody (apply su' tOut)
    tF                     = tXs :=> tOut

extTypesEnv :: TypeEnv -> [(Bind a, Type)] -> TypeEnv
extTypesEnv = foldr (\(x, t) -> extTypeEnv (bindId x) (Forall [] t))

funBind :: Maybe (Bind a) -> Type -> [(Bind a, Type)]
funBind (Just f) tF = [(f, tF)]
funBind _        _  = []

-----------------------------------------------------------------------------------------------
instApp :: (Located a) => SourceSpan -> TypeEnv -> Subst -> Poly -> [Expr a] -> (Subst, Type)
-----------------------------------------------------------------------------------------------
instApp sp env su sF       = tiApp sp su' env tF
  where
    (su', tF)              = instantiate su sF

-----------------------------------------------------------------------------------------------
tiApp :: (Located a) => SourceSpan -> Subst -> TypeEnv -> Type -> [Expr a] -> (Subst, Type)
-----------------------------------------------------------------------------------------------
tiApp sp su env tF eIns   = (su''', apply su''' tOut)
  where
    (su' , tIns)          = L.mapAccumL (ti env) su eIns
    (su'', tOut)          = freshTVar su'
    su'''                 = unify sp su'' tF (tIns :=> tOut)

-- HIDE
tupPoly, ifPoly :: Poly
tupPoly  = Forall ["a", "b"] (["a", "b"] :=> TPair "a" "b")
ifPoly   = Forall ["a"]      ([TBool, "a", "a"] :=> "a")

-- HIDE
fieldPoly :: Field -> Poly
fieldPoly Zero = Forall ["a", "b"] ([TPair "a" "b"] :=> "a")
fieldPoly One  = Forall ["a", "b"] ([TPair "a" "b"] :=> "b")

-- HIDE
prim2Poly :: Prim2 -> Poly
prim2Poly Plus    = Forall []    ([TInt, TInt] :=> TInt)
prim2Poly Minus   = Forall []    ([TInt, TInt] :=> TInt)
prim2Poly Times   = Forall []    ([TInt, TInt] :=> TInt)
prim2Poly Less    = Forall []    ([TInt, TInt] :=> TBool)
prim2Poly Greater = Forall []    ([TInt, TInt] :=> TBool)
prim2Poly Equal   = Forall ["a"] (["a" , "a" ] :=> TBool)

--------------------------------------------------------------------------------
unify :: SourceSpan -> Subst -> Type -> Type -> Subst
--------------------------------------------------------------------------------
unify sp su (ls :=> r) (ls' :=> r')
  | length ls == length ls'           = s2
  where
    s1                                = unifys sp su ls ls'
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
unifys :: SourceSpan -> Subst -> [Type] -> [Type] -> Subst
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
varAsgn :: SourceSpan -> Subst -> TVar -> Type -> Subst
--------------------------------------------------------------------------------
varAsgn sp su a t
  | t == TVar a          =  su
  | a `elem` freeTvars t =  abort (errOccurs sp a t)
  | otherwise            =  extSubst su a t

--------------------------------------------------------------------------------
generalize :: TypeEnv -> Type -> Poly
--------------------------------------------------------------------------------
generalize env t = Forall as t
  where
    as           = L.nub (tvs L.\\ evs)
    tvs          = freeTvars t
    evs          = freeTvars env

--------------------------------------------------------------------------------
instantiate :: Subst -> Poly -> (Subst, Type)
--------------------------------------------------------------------------------
instantiate su (Forall as t) = (su', apply suInst t)
  where
    (su', as')               = freshTVars su (length as)
    suInst                   = mkSubst (zip as as')

--------------------------------------------------------------------------------
-- | Environments --------------------------------------------------------------
--------------------------------------------------------------------------------

newtype TypeEnv = TypeEnv (M.Map Id Poly)

extTypeEnv :: Id -> Poly -> TypeEnv -> TypeEnv
extTypeEnv x s (TypeEnv env) =  TypeEnv $ M.insert x s env
  where
    -- _env  = traceShow _msg _env
    -- _msg  = "extTypeEnv: " ++ show x ++ " := " ++ show s

lookupTypeEnv :: SourceSpan -> Id -> TypeEnv -> Poly
lookupTypeEnv l x (TypeEnv env) = fromMaybe err  (M.lookup x env)
  where
    err                         = abort (errUnboundVar l x)

--------------------------------------------------------------------------------
-- | Substitutions -------------------------------------------------------------
--------------------------------------------------------------------------------
data Subst   = Su { suMap :: M.Map TVar Type
                  , suCnt :: !Int
                  }

empSubst :: Subst
empSubst =  Su M.empty 0

extSubst :: Subst -> TVar -> Type -> Subst
extSubst su a t = su { suMap = M.insert a t su' }
  where
     su'        = apply (mkSubst [(a, t)]) (suMap su)


mkSubst :: [(TVar, Type)] -> Subst
mkSubst ats = Su (M.fromList ats) 666

unSubst :: [TVar] -> Subst -> Subst
unSubst as su = su { suMap = foldr M.delete (suMap su) as }

freshTVars :: Subst -> Int -> (Subst, [Type])
freshTVars su n = L.mapAccumL (\a _ -> freshTVar a) su (replicate n ())

freshTVar :: Subst -> (Subst, Type)
freshTVar su = (su', TVar (TV ("a" ++ show i)))
  where
    (su', i) = fresh su

fresh :: Subst -> (Subst, Int)
fresh su  = (su {suCnt = n + 1}, n) where n = suCnt su

--------------------------------------------------------------------------------
-- Applying Substitutions ------------------------------------------------------
--------------------------------------------------------------------------------

class Substitutable a where
  apply     :: Subst -> a -> a
  freeTvars :: a -> [TVar]

instance Substitutable Type where
  apply _  TInt            = TInt
  apply _  TBool           = TBool
  apply su t@(TVar a)      = M.findWithDefault t a (suMap su)
  apply su (ts :=> t)      = apply su ts :=> apply su t
  apply su (TPair t1 t2)   = TPair (apply su t1) (apply su t2)
  apply su (TCtor c ts)    = TCtor c (apply su ts)

  freeTvars TInt           = []
  freeTvars TBool          = []
  freeTvars (TVar a)       = [a]
  freeTvars (ts :=> t)     = freeTvars ts ++ freeTvars t
  freeTvars (TPair t1 t2)  = freeTvars t1 ++ freeTvars t2
  freeTvars (TCtor _ ts)   = freeTvars ts

instance Substitutable Poly where
 apply s   (Forall as t) = Forall as $ apply (unSubst as s)  t
 freeTvars (Forall as t) = freeTvars t L.\\ as

instance (Functor t, Foldable t, Substitutable a) => Substitutable (t a) where
  apply     = fmap . apply
  freeTvars = foldr (\x r -> freeTvars x ++ r) []

instance Substitutable TypeEnv where
  apply s   (TypeEnv env) =  TypeEnv   (apply s <$> env)
  freeTvars (TypeEnv env) =  freeTvars (M.elems     env)

--------------------------------------------------------------------------------
-- Printing Types --------------------------------------------------------------
--------------------------------------------------------------------------------

instance Show Subst where
  show (Su m n) = show (m, n)

instance Show TypeEnv where
  showsPrec x (TypeEnv m) = showsPrec x (M.toList m)

instance Ex.Exception String where
