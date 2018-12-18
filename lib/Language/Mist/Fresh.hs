{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Language.Mist.Fresh (
     uniqify, uniqifyRType,
     varNum,

     FreshT (..),
     Fresh,

     runFreshT, execFreshT,

     ) where

import Control.Monad.State
import Control.Applicative (Alternative)
import Control.Monad.Identity (Identity, runIdentity)
-- import Control.Monad.Trans.Maybe
import qualified Data.Map.Strict as M
import Data.Maybe (fromJust)
import Data.List.Split (splitOn)

import Language.Mist.Types
import Language.Mist.Utils (safeTail)

cSEPARATOR = "##"
varNum :: Id -> Int
varNum = read . last . splitOn cSEPARATOR
createInternalName name number = name ++ cSEPARATOR ++ show number


--------------------------------------------------------------------------------
-- | A MonadFresh encompasses the operations for generating fresh, scoped names
--------------------------------------------------------------------------------
class Monad m => MonadFresh m where
  refreshId :: Id -> m Id         -- ^ generate a fresh name for the argument
  popId     :: Id -> m ()         -- ^ removes the most recent scoped version of a fresh name
  lookupId  :: Id -> m (Maybe Id) -- ^ gets the assigned fresh name

--------------------------------------------------------------------------------
-- Using a global (for all names) freshInt means we can pick up later
-- and not run into name collisions without having to refind all existing names.
--------------------------------------------------------------------------------
data FreshState = FreshState { nameMap :: M.Map Id [Id], freshInt :: Integer }

newtype FreshT m a = FreshT { unFreshT :: StateT FreshState m a }
 deriving (Functor, Applicative, Alternative, Monad, MonadPlus, MonadTrans)

type Fresh = FreshT Identity

instance Monad m => MonadFresh (FreshT m) where
  refreshId = genFreshId
  popId     = popScopedId
  lookupId  = getAssignedId

emptyFreshState :: FreshState
emptyFreshState = FreshState { nameMap = M.empty, freshInt = 0 }

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
  FreshT (modify $ \freshState@FreshState { nameMap = nameMap } ->
                     freshState { freshInt = newFreshInt
                                , nameMap = pushName name newName nameMap
                                })
  return newName

popScopedId :: (Monad m) => Id -> FreshT m ()
popScopedId name =
  FreshT (modify $ \freshState@FreshState { nameMap = newNameStack } ->
             freshState { nameMap = M.adjust safeTail name newNameStack })

getAssignedId :: (Monad m) => Id -> FreshT m (Maybe Id)
getAssignedId name =
  FreshT (gets $ fmap head . M.lookup name . nameMap)


-- | Run a computation with a fresh name supply.
runFreshT :: FreshT m a -> FreshState -> m (a, FreshState)
runFreshT (FreshT m) initialNames = runStateT m initialNames

evalFreshT :: Monad m => FreshT m a -> FreshState -> m a
evalFreshT (FreshT m) initialNames = evalStateT m initialNames

-- | Execute a computation with a fresh name supply.
execFreshT :: Monad m => FreshT m a -> FreshState -> m FreshState
execFreshT (FreshT m) initialNames = execStateT m initialNames

--------------------------------------------------------------------------------

uniqify :: Expr a -> Expr a
uniqify expr = runIdentity $ evalFreshT (uniqifyExpr expr) emptyFreshState

uniqifyExpr :: (MonadFresh m) => Expr a -> m (Expr a)
uniqifyExpr (Lam binds body extra) = do
  (newBinds, oldNames) <- unzip <$> mapM uniqifyBind binds
  newLam <- Lam newBinds <$> uniqifyExpr body <*> pure extra
  mapM_ popId (reverse oldNames)
  return newLam
uniqifyExpr (Let bind sig e1 e2 extra) = do
  (newBind, oldName) <- uniqifyBind bind
  newLet <- Let newBind <$> uniqifySig sig <*> uniqifyExpr e1 <*> uniqifyExpr e2 <*> pure extra
  popId oldName
  return newLet
uniqifyExpr (Id id extra) = do
  assignedName <- fmap fromJust $ lookupId id
  return $ Id assignedName extra

uniqifyExpr e@Number{} = pure e
uniqifyExpr e@Boolean{} = pure e
uniqifyExpr e@Unit{} = pure e
uniqifyExpr (Prim2 op e1 e2 extra) =
  Prim2 op <$> uniqifyExpr e1 <*> uniqifyExpr e2 <*> pure extra
uniqifyExpr (If e1 e2 e3 extra) =
  If <$> uniqifyExpr e1 <*> uniqifyExpr e2 <*> uniqifyExpr e3 <*> pure extra
uniqifyExpr (Tuple e1 e2 extra) =
  Tuple <$> uniqifyExpr e1 <*> uniqifyExpr e2 <*> pure extra
uniqifyExpr (GetItem e field extra) =
  GetItem <$> uniqifyExpr e <*> pure field <*> pure extra
uniqifyExpr (App e1 e2 extra) =
  App <$> uniqifyExpr e1 <*> uniqifyExpr e2 <*> pure extra

uniqifySig :: (MonadFresh m) => Sig a -> m (Sig a)
uniqifySig Infer = pure Infer
uniqifySig (Check r) = Check <$> uniqifyRPoly r
uniqifySig (Assume r) = Assume <$> uniqifyRPoly r

uniqifyRPoly :: (MonadFresh m) => RPoly Expr a -> m (RPoly Expr a)
uniqifyRPoly (RForall tvars r) = do
  (newTvars, oldNames) <- unzip <$> mapM uniqifyBindingTVar tvars
  newRForall <- RForall newTvars <$> uniqifyRType r
  mapM_ popId (reverse oldNames)
  return newRForall

uniqifyRType :: (MonadFresh m) => RType Expr a -> m (RType Expr a)
uniqifyRType (RBase bind typ expr) = do
  (newBind, oldName) <- uniqifyBind bind
  newRBase <- RBase newBind <$> uniqifyType typ <*> uniqifyExpr expr
  popId oldName
  return newRBase
uniqifyRType (RFun bind rtype1 rtype2) = do
  (newBind, oldName) <- uniqifyBind bind
  newRFun <- RFun newBind <$> uniqifyRType rtype1 <*> uniqifyRType rtype2
  popId oldName
  return newRFun
uniqifyRType (RRTy bind rtype expr) = do
  (newBind, oldName) <- uniqifyBind bind
  newRRTy <- RRTy newBind <$> uniqifyRType rtype <*> uniqifyExpr expr
  popId oldName
  return newRRTy

uniqifyType :: (MonadFresh m) => Type -> m Type
uniqifyType (TVar tvar) = TVar <$> uniqifyTVar tvar
uniqifyType TInt = pure TInt
uniqifyType TBool = pure TBool
uniqifyType (domain :=> codomain) =
  (:=>) <$> mapM uniqifyType domain <*> uniqifyType codomain
uniqifyType (TPair t1 t2) =
  TPair <$> uniqifyType t1 <*> uniqifyType t2
uniqifyType (TCtor c ts) =
  TCtor c <$> mapM uniqifyType ts

-- | returns the new binding and the original name
uniqifyBind :: (MonadFresh m) => Bind a -> m (Bind a, Id)
uniqifyBind (Bind name extra) = do
  newName <- refreshId name
  return (Bind newName extra, name)

-- | returns the new binding and the original name
uniqifyBindingTVar :: (MonadFresh m) => TVar -> m (TVar, Id)
uniqifyBindingTVar (TV name) = do
  newName <- refreshId name
  return (TV newName, name)

uniqifyTVar :: (MonadFresh m) => TVar -> m TVar
uniqifyTVar (TV name) = TV <$> (fromJust <$> lookupId name)
