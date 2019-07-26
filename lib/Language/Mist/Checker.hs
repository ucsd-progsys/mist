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
{-# LANGUAGE ConstraintKinds            #-}

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
    -- * type check and produce an elaborated expression
  , elaborate

    -- * Error Constructors
  , errUnboundVar
  , errUnboundFun

  , annotate
  ) where


import qualified Data.Map          as M
import qualified Data.Set          as S
import           Text.Printf (printf)
import           Control.Monad.State
import           Control.Monad.Except
import           Data.Foldable (fold)

import           Language.Mist.Types
import           Language.Mist.Utils
import           Language.Mist.Names

--------------------------------------------------------------------------------
-- | Well-formedness errors
--------------------------------------------------------------------------------

-- | Environment for well-formedness checks
-- Maintains recursive binders list to check for unannotated recursive binders
data WEnv = WEnv
  { binders :: [Id]
  , unannRecursiveBinders :: [Id]
  }

emptyWEnv = WEnv { binders = []
                 , unannRecursiveBinders = []
                 }

addBinder :: Bind t a -> WEnv -> WEnv
addBinder bind env@(WEnv{binders = binders})
  = env{binders = (bindId bind):binders}

addRecursiveBinder :: ParsedBind r a -> WEnv -> WEnv
addRecursiveBinder
  (AnnBind{bindId = x, bindAnn = Just ParsedInfer})
  env@(WEnv{unannRecursiveBinders = unannRecursiveBinders})
  = env{unannRecursiveBinders = x:unannRecursiveBinders}
addRecursiveBinder _ env = env

-- | `wellFormed e` returns the list of errors for an expression `e`
wellFormed :: (Located a) => ParsedExpr r a -> [UserError]
wellFormed = go emptyWEnv
  where
    go _ (Number n l)             = largeNumberErrors n (sourceSpan l)
    go _ Boolean{}                = []
    go _ Unit{}                   = []
    go env (Id x l)               = unboundVarErrors env x (sourceSpan l)
                                    ++ unannotatedRecursiveBinder env x (sourceSpan l)
    go _ Prim{}                   = []
    go env (If e1 e2 e3 _)        = go env e1
                                    ++ go env e2
                                    ++ go env e3
    go env (Let bind e1 e2 _)     = duplicateBindErrors env bind
                                    ++ go (addRecursiveBinder bind (addBinder bind env)) e1
                                    ++ go (addBinder bind env) e2
    go env (App e1 e2 _)          = go env e1
                                    ++ go env e2
    go env (Lam bind e _)         = go (addBinder bind env) e
    go env (TApp e _ _)           = go env e
    go env (TAbs _ e _)           = go env e

--------------------------------------------------------------------------------
-- | Error Checkers: In each case, return an empty list if no errors.
--------------------------------------------------------------------------------
duplicateBindErrors :: (Located a) => WEnv -> Bind t a -> [UserError]
duplicateBindErrors env bind
  = condError ((bindId bind) `elem` (binders env)) (errDupBind bind)

largeNumberErrors :: Integer -> SourceSpan -> [UserError]
largeNumberErrors n l
  = condError (maxInt < abs n) (errLargeNum l n)

maxInt :: Integer
maxInt = 1073741824

unboundVarErrors :: WEnv -> Id -> SourceSpan -> [UserError]
unboundVarErrors env x l
  = condError (x `notElem` (binders env)) (errUnboundVar l x)

unannotatedRecursiveBinder :: WEnv -> Id -> SourceSpan -> [UserError]
unannotatedRecursiveBinder env x l
  = condError (x `elem` (unannRecursiveBinders env)) (errUnannRecursiveBinder l x)

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
  show (VarBind id typ) = id ++ ":" ++ pprint typ
  show (BoundTVar tvar) = "$" ++ pprint tvar

-- | Ordered typing environment. Grows to the right.
-- Bindings can only depend on things to the left of themselves.
newtype TypeEnv = TypeEnv [TypeEnvPart]
  deriving (Show)

data Ctxt = Ctxt { typeEnv :: TypeEnv
                 , existentials :: S.Set TVar -- ^ The set of existential variables
                 , solutions :: TypeEnv -- ^ Keeps discarded solutions to be substituted in annotations
                 }

newtype TypingResult a = TypingResult {unTypingResult :: Result a}
  deriving (Monad, Applicative, Functor, MonadError [UserError])

type Context = StateT Ctxt (FreshT (StateT String TypingResult))

__debug = False

-- DEBUGGING
tell :: String -> Context ()
tell str = lift . lift . modify $ (\stuff -> stuff ++ str ++ "\n")

-- DEBUGGING
-- untell :: Context String
-- untell = lift get

initialCtxt :: Ctxt
initialCtxt = Ctxt { typeEnv = TypeEnv [], existentials = S.empty, solutions = TypeEnv [] }

evalContext :: Context a -> FreshState -> Result a
evalContext m freshState = unTypingResult $ evalStateT (evalFreshT (evalStateT m initialCtxt) freshState) ""

runContext :: Context a -> FreshState -> Result (a, String)
runContext m freshState = unTypingResult $ runStateT (evalFreshT (evalStateT m initialCtxt) freshState) ""

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

getsEnv :: (TypeEnv -> a) -> Context a
getsEnv f = gets $ f . typeEnv

getEnv :: Context TypeEnv
getEnv = getsEnv id

modifyEnv :: (TypeEnv -> TypeEnv) -> Context ()
modifyEnv f = modify $ \ctxt@Ctxt{typeEnv = env} -> ctxt{typeEnv = f env}

setEnv :: TypeEnv -> Context ()
setEnv newEnv = modifyEnv $ const newEnv

-- | Extends the environment adding new existentials to solutions
extendEnv :: [TypeEnvPart] -> Context ()
extendEnv newParts = do
  modifyEnv $ envAppend newParts
  modify $ \ctxt@Ctxt{solutions = sols} -> ctxt{solutions = envAppend (filter evarFilter newParts) sols}
  where
    envAppend newParts (TypeEnv env) = TypeEnv $ env `mappend` newParts

    evarFilter Unsolved{} = True
    evarFilter Solved{} = True
    evarFilter _ = False

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

generateExistential :: Context EVar
generateExistential = do
  newEvar <- TV <$> refreshId "E?"
  modify $ \ctxt@Ctxt{existentials = existSet} -> ctxt { existentials = S.insert newEvar existSet}
  pure newEvar

toEVar :: Type -> Context (Maybe EVar)
toEVar (TVar tvar) = do
  isEVar <- gets $ S.member tvar . existentials
  if isEVar then pure $ Just tvar else pure Nothing
toEVar _ = pure Nothing

unsolvedExistentials :: TypeEnv -> [EVar]
unsolvedExistentials (TypeEnv env) = [evar | (Unsolved evar) <- env]

--------------------------------------------------------------------------------
-- Elaboration -----------------------------------------------------------------
--------------------------------------------------------------------------------

type ElaborateConstraints r a = (Located a, PPrint r)

-- | Elaborates a surface Expr
-- - adds type annotations
-- - adds explicit type application
-- - adds explicit type abstraction
-- - assumes every name is unique
elaborate :: ElaborateConstraints r a => ParsedExpr r a -> Result (ElaboratedExpr r a)
elaborate e =
  if __debug
  then do
    (result, log) <- runContext (elaborateAndSubst e) emptyFreshState
    pure $ trace log result
  else evalContext (elaborateAndSubst e) emptyFreshState -- TODO: pass around the name state

  where
    elaborateAndSubst e = do
      (elaborated, _) <- synthesize e
      Ctxt{solutions = sols} <- get
      pure $ subst (envToSubst sols) elaborated


-- DEBUGGING
synthesize :: ElaborateConstraints r a => ParsedExpr r a -> Context (ElaboratedExpr r a, Type)
synthesize e = do
  env <- getEnv
  tell $ show env ++ " ⊢ " ++ pprint e ++ " =>"
  _synthesize e

-- TODO: add judgments for documentation
-- | Γ ⊢ e ~> c => A ⊣ Θ
_synthesize (Number i l) = pure (Number i l, TInt)
_synthesize (Boolean b l) = pure (Boolean b l, TBool)
_synthesize (Unit l) = pure (Unit l, TUnit)
_synthesize (Id id l) = do
  boundType <- getsEnv $ getBoundType id
  case boundType of
    Just typ -> pure (Id id l, typ)
    Nothing -> throwError $ [errUnboundVar (sourceSpan l) id]
_synthesize (Prim prim l) = do
   typ <- primType prim
   pure (Prim prim l, typ)
_synthesize (If condition e1 e2 l) = do -- TODO: how to properly handle synthesis of branching
  cCondition <- check condition TBool
  alpha <- generateExistential
  extendEnv [Unsolved alpha]
  c1 <- check e1 (EVar alpha)
  env <- getEnv
  let firstBranchType = applyEnv env (EVar alpha)
  c2 <- check e2 firstBranchType
  env' <- getEnv
  pure (If cCondition c1 c2 l, applyEnv env' firstBranchType)
_synthesize (Let binding e1 e2 l) =
  typeCheckLet binding e1 e2 l
  (\annBind c1 e2 l -> do
      (c2, inferredType) <- _synthesize e2
      pure (Let annBind c1 c2 l, inferredType))
_synthesize (App e1 e2 l) = do
  (c1, funType) <- synthesize e1
  env <- getEnv
  synthesizeApp (applyEnv env funType) c1 e2 l
_synthesize (Lam bind e l) = do
  alpha <- generateExistential
  beta <- generateExistential
  let newBinding = VarBind (bindId bind) (EVar alpha)
  extendEnv [Unsolved alpha, Unsolved beta, newBinding]
  c <- check e (EVar beta)
  modifyEnv $ dropEnvAfter newBinding
  let annBind = bind{bindAnn = Just $ ElabUnrefined (EVar alpha)}
  pure (Lam annBind c l, EVar alpha :=> EVar beta)
_synthesize (TApp _e _typ _l) = error "TODO"
_synthesize (TAbs _alpha _e _l) = error "TODO"

-- DEBUGGING
check :: ElaborateConstraints r a => ParsedExpr r a -> Type -> Context (ElaboratedExpr r a)
check e t = do
  env <- getEnv
  tell $ show env ++ " ⊢ " ++ pprint e ++ " <= " ++ pprint t
  _check e t

-- | Γ ⊢ e ~> c <= A ⊣ Θ
_check expr (TForall tvar typ) = do
  extendEnv [BoundTVar tvar]
  c <- check expr typ
  modifyEnv $ dropEnvAfter (BoundTVar tvar)
  pure c
_check expr typ = do
  maybeEVar <- toEVar typ
  case maybeEVar of
    Just _  -> checkSub expr typ
    Nothing -> go expr typ

  where
    go (Number i l) TInt = pure $ Number i l
    go (Boolean b l) TBool = pure $ Boolean b l
    go e@Id{} t = checkSub e t
    go e@Prim{} t = checkSub e t
    go (If condition e1 e2 l) t = do
      cCondition <- check condition TBool
      c1 <- check e1 t
      c2 <- check e2 t
      pure $ If cCondition c1 c2 l
    go (Let binding e1 e2 l) t =
      typeCheckLet binding e1 e2 l
      (\annBind c1 e2 l -> do
          c2 <- check e2 t
          pure $ Let annBind c1 c2 l)
    go e@App{} t = checkSub e t
    go (Lam bind e l) (t1 :=> t2) = do
      let newBinding = VarBind (bindId bind) t1
      extendEnv [newBinding]
      c <- check e t2
      modifyEnv $ dropEnvAfter newBinding
      let annBind = bind{bindAnn = Just $ ElabUnrefined t1}
      pure $ Lam annBind c l
    go (Unit l) TUnit = pure $ Unit l
    go (TApp _e _typ _l) _ = error "TODO"
    go (TAbs _alpha _e _l) _ = error "TODO"
    go e typ = throwError $ [errCheckingError (sourceSpan e) typ]

synthesizeApp :: ElaborateConstraints r a => Type -> ElaboratedExpr r a -> ParsedExpr r a -> a -> Context (ElaboratedExpr r a, Type)
synthesizeApp tFun cFun eArg l = do
  (cInstantiatedFun, cArg, resultType) <- synthesizeSpine tFun cFun eArg
  pure (App cInstantiatedFun cArg l, resultType)

-- DEBUGGING
synthesizeSpine :: ElaborateConstraints r a => Type -> ElaboratedExpr r a -> ParsedExpr r a -> Context (ElaboratedExpr r a, ElaboratedExpr r a, Type)
synthesizeSpine funType cFun eArg = do
  env <- getEnv
  tell $ show env ++ " ⊢ " ++ pprint funType ++ " • " ++ pprint eArg ++ " >>"
  _synthesizeSpine funType cFun eArg

-- | Γ ⊢ A_c • e ~> (cFun, cArg) >> C ⊣ Θ
_synthesizeSpine :: ElaborateConstraints r a => Type -> ElaboratedExpr r a -> ParsedExpr r a -> Context (ElaboratedExpr r a, ElaboratedExpr r a, Type)
_synthesizeSpine funType cFun eArg = do
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
      let annotatedFun = putAnn (Just $ ElabUnrefined (EVar alpha1 :=> EVar alpha2)) cFun
      pure (annotatedFun, cArg, EVar alpha2)

    go (t1 :=> t2) = do
      cArg <- check eArg t1
      pure (putAnn (Just $ ElabUnrefined (t1 :=> t2)) cFun, cArg, t2)
    go tforall@(TForall (TV tv) t) = do
      evar <- generateExistential
      extendEnv [Unsolved evar]
      let newFunType = subst (tv |-> (EVar evar)) t
      let annotatedFun = (putAnn (Just $ ElabUnrefined tforall) cFun)
      synthesizeSpine newFunType (putAnn (Just $ ElabUnrefined newFunType) (TApp annotatedFun (EVar evar) (extractLoc cFun))) eArg
    go t = throwError $ [errApplyNonFunction (sourceSpan cFun) t]

-- | Γ ⊢ A_c <: B ~> c ⊣ Θ
-- When doing a ∀A.B <: C the subtyping check will infer the
-- polymorphic instantiation for c.
instSub :: ElaboratedExpr r a -> Type -> Type -> Context (ElaboratedExpr r a)
instSub c a@(TForall _ _) b =
  foldr (\typ instantiated -> TApp (putAnn (Just $ ElabUnrefined a) instantiated) typ (extractLoc c))
        c <$> go a b

  where
    go (TForall alpha a) b = do
      evar <- generateExistential
      extendEnv [Scope evar, Unsolved evar]
      instantiations <- go (subst ((unTV alpha) |-> (EVar evar)) a) b
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
(<:) :: Type -> Type -> Context ()
a <: b = do
  env <- getEnv
  tell $ show env ++ " ⊢ " ++ pprint a ++ " <: " ++ pprint b
  a <<: b

-- | Γ ⊢ A <: B ⊣ Θ
(<<:) :: Type -> Type -> Context ()
TUnit <<: TUnit = pure ()
TInt <<: TInt = pure ()
TBool <<: TBool = pure ()
a@(TVar _) <<: b@(TVar _) | a == b = pure ()
(a1 :=> a2) <<: (b1 :=> b2) = do
  b1 <: a1
  env <- getEnv
  (applyEnv env a2) <: (applyEnv env b2)
(TCtor ctor1 as) <<: (TCtor ctor2 bs)
  | ctor1 /= ctor2 = error $ "TODO: constructor mismatch" ++ show ctor1 ++ show ctor2
  | otherwise =
    if length as /= length bs
      then error "TODO: constructor application length mismatch"
      else mapM_ (\(a, b) -> do
                    env <- getEnv
                    (applyEnv env a) <: (applyEnv env b))
                  (zip (snd <$> as) (snd <$> bs))
(TForall alpha a) <<: b = do
  evar <- generateExistential
  extendEnv [Scope evar, Unsolved evar]
  (subst ((unTV alpha) |-> (EVar evar)) a) <: b
  modifyEnv $ dropEnvAfter (Scope evar)
a <<: (TForall alpha b) = do
  extendEnv [BoundTVar alpha]
  a <: b
  modifyEnv $ dropEnvAfter (BoundTVar alpha)
a <<: b = do
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
    (_, _) -> error $ "TODO: this is a subtyping error: " ++ show a ++ " <: " ++ show b

-- DEBUGGING
instantiateL :: EVar -> Type -> Context ()
instantiateL a b = do
  env <- getEnv
  tell $ show env ++ " ⊢ " ++ pprint a ++ " <=: " ++ pprint b
  _instantiateL a b

-- TODO: figure out why we reverse the newly created existentials
_instantiateL :: EVar -> Type -> Context ()
_instantiateL alpha typ = do
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
    go (TCtor ctor vts) = do
      let (vs, as) = unzip vts
      betas <- mapM (const generateExistential) as
      solveExistential alpha (TCtor ctor (zip vs $ fmap EVar betas)) (reverse betas)
      mapM_ (\(beta, a) -> do
                env <- getEnv
                instantiateL beta (applyEnv env a))
            (zip betas as)
    go (TForall tvar a) = do
      extendEnv [BoundTVar tvar]
      instantiateL alpha a
      modifyEnv $ dropEnvAfter (BoundTVar tvar)
    go typ = solveExistential alpha typ []

-- DEBUGGING
instantiateR :: Type -> EVar -> Context ()
instantiateR a b = do
  env <- getEnv
  tell $ show env ++ " ⊢ " ++ pprint a ++ " :=> " ++ pprint b
  _instantiateR a b

_instantiateR :: Type -> EVar -> Context ()
_instantiateR typ alpha = do
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
    go (TCtor ctor vts) = do
      let (vs, as) = unzip vts
      betas <- mapM (const generateExistential) as
      solveExistential alpha (TCtor ctor (zip vs $ fmap EVar betas)) (reverse betas)
      mapM_ (\(a, beta) -> do
                env <- getEnv
                instantiateR (applyEnv env a) beta)
            (zip as betas)
    go (TForall tvar a) = do
      beta <- generateExistential
      extendEnv [Scope beta, Unsolved beta]
      instantiateR (subst ((unTV tvar) |-> (EVar beta)) a) alpha
      modifyEnv $ dropEnvAfter (Scope beta)
    go typ = solveExistential alpha typ []

assertLeftOf :: EVar -> EVar -> Context ()
alpha `assertLeftOf` beta = do
  alphaToLeft <- getsEnv $ alpha `isLeftOf` beta
  if alphaToLeft
    then pure ()
    else error (printf "TODO: expected Γ[%0$s][%1$s] but got Γ[%1$s][%2$s]" (show alpha) (show beta))

occurrenceCheck :: EVar -> Type -> Context ()
occurrenceCheck alpha typ = do
  evars <- freeEVars typ
  if S.member alpha evars
    then throwError $ [errInfiniteTypeConstraint alpha typ]
    else pure ()

primType :: (MonadFresh m) => Prim -> m Type
primType Plus    = pure $ TInt :=> (TInt :=> TInt)
primType Minus   = pure $ TInt :=> (TInt :=> TInt)
primType Times   = pure $ TInt :=> (TInt :=> TInt)
primType Less    = pure $ TInt :=> (TInt :=> TBool)
primType Greater = pure $ TInt :=> (TInt :=> TBool)
primType Lte     = pure $ TInt :=> (TInt :=> TBool)
primType Union   = do
  a <- refreshId $ "a" ++ cSEPARATOR
  let sa = setType $ TVar $ TV a
  pure $ TForall (TV a) (sa :=> sa :=> sa)
primType Elem    = do
  a <- refreshId $ "a" ++ cSEPARATOR
  let sa = setType $ TVar $ TV a
  pure $ TForall (TV a) (sa :=> TVar (TV a) :=> TBool)
primType SetAdd  = do
  a <- refreshId $ "a" ++ cSEPARATOR
  let sa = setType $ TVar $ TV a
  pure $ TForall (TV a) (sa :=> TVar (TV a) :=> sa)
primType SetDel  = do
  a <- refreshId $ "a" ++ cSEPARATOR
  let sa = setType $ TVar $ TV a
  pure $ TForall (TV a) (sa :=> TVar (TV a) :=> sa)
primType SetSub  = do
  a <- refreshId $ "a" ++ cSEPARATOR
  let sa = setType $ TVar $ TV a
  pure $ TForall (TV a) (sa :=> sa :=> TBool)

primType Store = do
  k <- refreshId $ "k" ++ cSEPARATOR
  let tk = TVar $ TV k
  v <- refreshId $ "v" ++ cSEPARATOR
  let tv = TVar $ TV v
  pure $ TForall (TV k) $ TForall (TV v) $ mapType tk tv :=> tk :=> tv :=> mapType tk tv

primType Equal   = do
  a <- refreshId $ "a" ++ cSEPARATOR
  pure $ TForall (TV a) ((TVar $ TV a) :=> ((TVar $ TV a) :=> TBool))
primType And     = pure $ TBool :=> (TBool :=> TBool)

checkSub :: ElaborateConstraints r a => ParsedExpr r a -> Type -> Context (ElaboratedExpr r a)
checkSub e t1 = do
  (c, t2) <- synthesize e
  env <- getEnv
  instSub c (applyEnv env t2) (applyEnv env t1)

typeCheckLet ::
  ElaborateConstraints r a =>
  ParsedBind r a ->
  ParsedExpr r a ->
  ParsedExpr r a ->
  a ->
  (ElaboratedBind r a -> ElaboratedExpr r a -> ParsedExpr r a -> a -> Context b) ->
  Context b
typeCheckLet binding@(AnnBind{bindAnn = Just ParsedInfer}) e1 e2 tag handleBody = do
  alpha <- generateExistential
  let evar = EVar alpha
  extendEnv [Scope alpha, Unsolved alpha, VarBind (bindId binding) evar]
  unsubstitutedC1 <- check e1 evar
  (delta, delta') <- getsEnv $ splitEnvAt (Scope alpha)
  setEnv delta
  (boundType, c1) <- letGeneralize evar unsubstitutedC1 delta'
  let newBinding = VarBind (bindId binding) boundType
  extendEnv [newBinding]
  let annBind = binding{bindAnn = Just $ ElabUnrefined boundType}
  result <- handleBody annBind c1 e2 tag
  modifyEnv $ dropEnvAfter newBinding
  pure result
typeCheckLet binding@(AnnBind{bindAnn = Just (ParsedCheck rType)}) e1 e2 tag handleBody = do
  let typ = eraseRType rType
  let newBinding = VarBind (bindId binding) typ
  extendEnv [newBinding]
  unabstractedC1 <- check e1 typ
  let c1 = insertTAbs typ unabstractedC1
  let annBind = binding{bindAnn = Just $ ElabRefined rType}
  result <- handleBody annBind c1 e2 tag
  modifyEnv $ dropEnvAfter newBinding
  pure result
typeCheckLet binding@(AnnBind{bindAnn = Just (ParsedAssume rType)}) e1 e2 tag handleBody = do
  let typ = eraseRType rType
  let newBinding = VarBind (bindId binding) typ
  extendEnv [newBinding]
  (c1, _) <- synthesize e1
  let annBind = binding{bindAnn = Just $ ElabAssume rType}
  result <- handleBody annBind c1 e2 tag
  modifyEnv $ dropEnvAfter newBinding
  pure result
typeCheckLet AnnBind{bindAnn = Nothing} _ _ _ _ =
  error "impossible: every binder should be annotated"

-- | Carries out Hindley-Milner style let generalization on the existential variable.
-- Also substitutes for all existentials that were added as annotations
letGeneralize :: Type -> ElaboratedExpr r a -> TypeEnv -> Context (Type, ElaboratedExpr r a)
letGeneralize t c env = do
  let preGeneralizedFun = applyEnv env t
  freeExistentials <- freeEVars preGeneralizedFun
  let unsolvedAlphas = filter (`elem` freeExistentials) (unsolvedExistentials env)
  pairedNewTvars <- mapM (\alpha -> do
                             a <- TV <$> refreshId ("a" ++ cSEPARATOR) -- TODO: special character for inferred type variables
                             pure (alpha, a))
                    unsolvedAlphas
  let substitution = M.fromList $ fmap (\(alpha, a) -> (unTV alpha, TVar a)) pairedNewTvars
  let generalizedType = if null pairedNewTvars
        then preGeneralizedFun
        else foldr (\(_, a) accType -> TForall a accType) (subst substitution preGeneralizedFun) pairedNewTvars
  let abstractedFun = insertTAbs generalizedType c
  pure (generalizedType, subst substitution abstractedFun)

-- selectorToPrim :: Field -> a -> ElaboratedExpr r a
-- selectorToPrim Zero tag = CPrim Pi0 tag
-- selectorToPrim One tag = CPrim Pi1 tag

-- selectorToType :: Field -> Context Type
-- selectorToType Zero = do
--   tvar0 <- TV <$> refreshId "a"
--   tvar1 <- TV <$> refreshId "b"
--   pure $ TForall tvar0 (TForall tvar1 (TPair (TVar tvar0) (TVar tvar1) :=> TVar tvar0))
-- selectorToType One = do
--   tvar0 <- TV <$> refreshId "a"
--   tvar1 <- TV <$> refreshId "b"
--   pure $ TForall tvar0 (TForall tvar1 (TPair (TVar tvar0) (TVar tvar1) :=> TVar tvar1))

-- | Solves an unsolved existential.
-- If this new solution introduces new existentials
-- these are added immediately before the existential we are solving.
-- Errors if the existential does not exist or has already been solved.
solveExistential :: EVar -> Type -> [EVar] -> Context ()
solveExistential evar partialSolution newEvars = do
  Ctxt{typeEnv = (TypeEnv env), solutions = (TypeEnv sols)} <- get
  newEnv <- replaceUnsolved env
  newSols <- replaceUnsolved sols
  modify $ \ctxt -> ctxt{typeEnv = TypeEnv newEnv, solutions = TypeEnv newSols}
  where

    replaceUnsolved [] = error "attempting to articulate nonexistent existential"
    replaceUnsolved (Unsolved evar':parts)
      | evar' == evar = pure $ fmap Unsolved newEvars
                               `mappend` [Solved evar partialSolution]
                               `mappend` parts
    replaceUnsolved (Solved evar' _:_)
      | evar' == evar = throwError $ [errSolvingSolvedExistential]
    replaceUnsolved (part:parts) = (part:) <$> replaceUnsolved parts

freeEVars :: Type -> Context (S.Set EVar)
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
    -- eVars (TPair t1 t2) = S.union <$> eVars t1 <*> eVars t2
    eVars (TCtor _ ts) = fold <$> mapM eVars (snd <$> ts)
    eVars (TForall _ t) = eVars t

insertTAbs :: Type -> ElaboratedExpr r a -> ElaboratedExpr r a
insertTAbs (TForall tvar typ) c = TAbs tvar (insertTAbs typ c) (extractLoc c)
insertTAbs _ c = c

--------------------------------------------------------------------------------
-- | Error Constructors
--------------------------------------------------------------------------------

condError :: Bool -> UserError -> [UserError]
condError True  e = [e]
condError False _ = []

errDupBind x = mkError (printf "Shadow binding '%s'" (bindId x)) (sourceSpan x)
errLargeNum l n = mkError (printf "Number '%d' is too large" n) l
errUnboundVar l x = mkError (printf "Unbound variable '%s'" x) l
errUnboundFun l f = mkError (printf "Function '%s' is not defined" f) l
errUnannRecursiveBinder l x = mkError (printf "Recursive function %s must be annotated" (show x)) l
errSolvingSolvedExistential = error "TODO: solving solved existential"
errApplyNonFunction l typ = mkError (printf "Applying non-function of type %s" (show typ)) l
errInfiniteTypeConstraint _ _ = error "TODO: infinite type constraint"
errCheckingError l typ = mkError (printf "Checking expression has type %s failed" (show typ)) l

--------------------------------------------------------------------------------
-- | Annotate
--------------------------------------------------------------------------------
type AnnotationContext r a = M.Map Id Type

annotate :: ElaborateConstraints r a => ElaboratedExpr r a -> Type -> ElaboratedExpr r a
annotate e typ = runFresh $ go M.empty e typ
  where
    go :: ElaborateConstraints r a => AnnotationContext r a -> ElaboratedExpr r a -> Type -> Fresh (ElaboratedExpr r a)
    go _ (Number n l) _ = pure $ AnnNumber n (ann TInt) l
    go _ (Boolean b l) _ = pure $ AnnBoolean b (ann TBool) l
    go _ (Unit l) _ = pure $ AnnUnit (ann TUnit) l
    go _ (Prim op l) _ = AnnPrim op <$> fmap ann (primType op) <*> pure l
    go ctxt (Id x l) _ = pure $ AnnId x (ann (ctxt M.! x)) l
    go ctxt (If condition e1 e2 l) typ =
      AnnIf <$> go ctxt condition TBool <*> go ctxt e1 typ <*> go ctxt e2 typ <*> pure (ann typ) <*> pure l
    go ctxt (Let bind@(AnnBind _ (Just ElabAssume{}) _) e1 e2 l) typ =
      let boundType = eraseElaboratedAnn $ bindAnn bind
          ctxt' = M.insert (bindId bind) boundType ctxt in
      AnnLet bind e1 <$> go ctxt' e2 typ <*> pure (ann typ) <*> pure l
    go ctxt (Let bind e1 e2 l) typ =
      let boundType = eraseElaboratedAnn $ bindAnn bind
          ctxt' = M.insert (bindId bind) boundType ctxt in
      AnnLet bind <$> go ctxt' e1 boundType <*> go ctxt' e2 typ <*> pure (ann typ) <*> pure l
    go ctxt (App e1 e2 l) typ =
      let tFun = eraseElaboratedAnn $ extractAnn e1
          (t1 :=> _) = tFun in
      AnnApp <$> go ctxt e1 tFun <*> go ctxt e2 t1 <*> pure (ann typ) <*> pure l
    go ctxt (Lam bind e l) typ@(t1 :=> t2) =
      let ctxt' = M.insert (bindId bind) t1 ctxt in
      AnnLam bind <$> go ctxt' e t2 <*> pure (ann typ) <*> pure l
    go ctxt (TApp e t l) typ =
      let tAbs = eraseElaboratedAnn $ extractAnn e in
      AnnTApp <$> go ctxt e tAbs <*> pure t <*> pure (ann typ) <*> pure l
    go ctxt (TAbs tvar e l) tAbs@(TForall _ typ) = AnnTAbs tvar <$> go ctxt e typ <*> pure (ann tAbs) <*> pure l
    go _ expr typ = error $ "incorrectly-typed elaborated expression: " ++ pprint expr ++ " : " ++ pprint typ

    ann typ = Just $ ElabUnrefined typ

    eraseElaboratedAnn (Just (ElabRefined rtype)) = eraseRType rtype
    eraseElaboratedAnn (Just (ElabAssume rtype)) = eraseRType rtype
    eraseElaboratedAnn (Just (ElabUnrefined typ)) = typ
    eraseElaboratedAnn Nothing = error "impossible: should be annotated"
