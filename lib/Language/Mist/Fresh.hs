{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Language.Mist.Fresh
  (
  ) where

import Control.Monad.State
import qualified Data.Map.Strict as M
import Data.Maybe (fromJust)
import Language.Mist.Types
import Language.Mist.Utils (safeTail)
import Control.Applicative (Alternative)
import Control.Monad.Identity (Identity, runIdentity)

-- | TODO: should this separate type variables and term variables?
-- | A MonadFresh encompasses the operations for generating fresh, scoped names
class Monad m => MonadFresh a m where
  genFreshName :: a -> m a             -- ^ generate a fresh name for the argument
  popScopedName :: a -> m ()           -- ^ removes the most recent scoped version of a fresh name
  getAssignedName :: a -> m (Maybe a)  -- ^ gets the assigned fresh name


createInternalName :: Id -> Integer -> Id
createInternalName name number = name ++ "##" ++ show number

-- Using a global (for all names) freshInt means we can pick up later
-- and not run into name collisions without having to refind all existing names.
data FreshState = FreshState { newNameMap :: M.Map Id [Id], freshInt :: Integer }

newtype FreshT m a = FreshT { unFreshT :: StateT FreshState m a }
 deriving (Functor, Applicative, Alternative, Monad, MonadPlus, MonadTrans)

newtype Fresh a = Fresh { unFresh :: FreshT Identity a }
 deriving (Functor, Applicative, Monad)

instance MonadFresh Id Fresh where
  genFreshName = Fresh . genFreshId
  popScopedName = Fresh . popScopedId
  getAssignedName = Fresh . getAssignedId

emptyFreshState :: FreshState
emptyFreshState = FreshState { newNameMap = M.empty
                             , freshInt = 0
                             }

-- | pushes a new name onto the name stack
pushName :: Id -> Id -> M.Map Id [Id] -> M.Map Id [Id]
pushName oldName newName nameMap =
  M.insertWith (\[newName] newNameStack -> newName:newNameStack)
               oldName [newName] nameMap

genFreshId :: (Monad m) => Id -> FreshT m Id
genFreshId name = do
  FreshState { freshInt = currentFreshInt } <- FreshT get
  let newFreshInt = currentFreshInt + 1
      newName = createInternalName name currentFreshInt
  FreshT (modify $ \freshState@FreshState { newNameMap = newNameMap } ->
                     freshState { freshInt = newFreshInt
                                , newNameMap = pushName name newName newNameMap
                                })
  return newName

popScopedId :: (Monad m) => Id -> FreshT m ()
popScopedId name =
  FreshT (modify $ \freshState@FreshState { newNameMap = newNameStack } ->
             freshState { newNameMap = M.adjust safeTail name newNameStack })

getAssignedId :: (Monad m) => Id -> FreshT m (Maybe Id)
getAssignedId name =
  FreshT (gets $ fmap head . M.lookup name . newNameMap)


-- | Run a computation with a fresh name supply.
runFreshT :: FreshT m a -> FreshState -> m (a, FreshState)
runFreshT (FreshT m) initialNames = runStateT m initialNames

evalFreshT :: Monad m => FreshT m a -> FreshState -> m a
evalFreshT (FreshT m) initialNames = evalStateT m initialNames

-- | Execute a computation with a fresh name supply.
execFreshT :: Monad m => FreshT m a -> FreshState -> m FreshState
execFreshT (FreshT m) initialNames = execStateT m initialNames

evalFresh :: Fresh a -> FreshState -> a
evalFresh (Fresh s) initialNames = runIdentity $ evalFreshT s initialNames


uniqify :: Expr a -> Expr a
uniqify expr = evalFresh (uniqifyExpr expr) emptyFreshState

uniqifyExpr :: (MonadFresh Id m) => Expr a -> m (Expr a)
uniqifyExpr e@Number{} = pure e
uniqifyExpr e@Boolean{} = pure e
uniqifyExpr (Id id extra) = do
  assignedName <- fmap fromJust $ getAssignedName id
  return $ Id assignedName extra
uniqifyExpr (Prim2 op e1 e2 extra) =
  Prim2 op <$> uniqifyExpr e1 <*> uniqifyExpr e2 <*> pure extra
uniqifyExpr (If e1 e2 e3 extra) =
  If <$> uniqifyExpr e1 <*> uniqifyExpr e2 <*> uniqifyExpr e3 <*> pure extra
uniqifyExpr (Let bind sig e1 e2 extra) = do
  (newBind, oldName) <- uniqifyBind bind
  newLet <- Let newBind <$> uniqifySig sig <*> uniqifyExpr e1 <*> uniqifyExpr e2 <*> pure extra
  popScopedName oldName
  return newLet
uniqifyExpr (Tuple e1 e2 extra) =
  Tuple <$> uniqifyExpr e1 <*> uniqifyExpr e2 <*> pure extra
uniqifyExpr (GetItem e field extra) =
  GetItem <$> uniqifyExpr e <*> pure field <*> pure extra
uniqifyExpr (App e1 e2 extra) =
  App <$> uniqifyExpr e1 <*> uniqifyExpr e2 <*> pure extra
uniqifyExpr (Lam binds body extra) = do
  (newBinds, oldNames) <- unzip <$> mapM uniqifyBind binds
  newLam <- Lam newBinds <$> uniqifyExpr body <*> pure extra
  mapM_ popScopedName (reverse oldNames)
  return newLam
uniqifyExpr e@Unit{} = pure e

uniqifySig :: (MonadFresh Id m) => Sig a -> m (Sig a)
uniqifySig Infer = pure Infer
uniqifySig (Check r) = Check <$> uniqifyRPoly r
uniqifySig (Assume r) = Assume <$> uniqifyRPoly r

uniqifyRPoly :: (MonadFresh Id m) => RPoly a -> m (RPoly a)
uniqifyRPoly (RForall tvars r) = do
  (newTvars, oldNames) <- unzip <$> mapM uniqifyBindingTVar tvars
  newRForall <- RForall newTvars <$> uniqifyRType r
  mapM_ popScopedName (reverse oldNames)
  return newRForall

uniqifyRType :: (MonadFresh Id m) => RType a -> m (RType a)
uniqifyRType (RBase bind typ expr) = do
  (newBind, oldName) <- uniqifyBind bind
  newRBase <- RBase newBind <$> uniqifyType typ <*> uniqifyExpr expr
  popScopedName oldName
  return newRBase
unqifyRType (RFun bind rtype1 rtype2) = do
  (newBind, oldName) <- uniqifyBind bind
  newRFun <- RFun newBind <$> uniqifyRType rtype1 <*> uniqifyRType rtype2
  popScopedName oldName
  return newRFun
unqifyRType (RRTy bind rtype expr) = do
  (newBind, oldName) <- uniqifyBind bind
  newRRTy <- RRTy newBind <$> uniqifyRType rtype <*> uniqifyExpr expr
  popScopedName oldName
  return newRRTy

uniqifyType :: (MonadFresh Id m) => Type -> m Type
uniqifyType (TVar tvar) = TVar <$> uniqifyTVar tvar
uniqifyTyp TInt = pure TInt
uniqifyTyp TBool = pure TBool
uniqifyTyp (domain :=> codomain) =
  (:=>) <$> mapM uniqifyTyp domain <*> uniqifyTyp codomain
uniqifyTyp (TPair t1 t2) =
  TPair <$> uniqifyTyp t1 <*> uniqifyTyp t2
uniqifyTyp (TCtor c ts) =
  TCtor c <$> mapM uniqifyTyp ts

-- | returns the new binding and the original name
uniqifyBind :: (MonadFresh Id m) => Bind a -> m (Bind a, Id)
uniqifyBind (Bind name extra) = do
  newName <- genFreshName name
  return (Bind newName extra, name)

-- | returns the new binding and the original name
uniqifyBindingTVar :: (MonadFresh Id m) => TVar -> m (TVar, Id)
uniqifyBindingTVar (TV name) = do
  newName <- genFreshName name
  return (TV newName, name)

uniqifyTVar :: (MonadFresh Id m) => TVar -> m TVar
uniqifyTVar (TV name) = TV <$> (fromJust <$> getAssignedName name)
