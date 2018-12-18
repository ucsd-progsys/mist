{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}

module Language.Mist.Fresh (
     uniqify, uniqifyRType,
     varNum,

     FreshT,
     Fresh,

     ) where

import Control.Monad.State
import Control.Monad.Identity (Identity)
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
  popId     :: m ()               -- ^ removes the most recent scoped version of a fresh name
  lookupId  :: Id -> m (Maybe Id) -- ^ gets the assigned fresh name

--------------------------------------------------------------------------------
-- Using a global (for all names) freshInt means we can pick up later
-- and not run into name collisions without having to refind all existing names.
--------------------------------------------------------------------------------
data FreshState = FreshState { nameMap :: M.Map Id [Id], freshInt :: Integer, ctx :: [Id] }
type FreshT = StateT FreshState
type Fresh = FreshT Identity

instance Monad m => MonadFresh (FreshT m) where
  refreshId name = do
    FreshState m n g <- get
    let n' = n + 1
        name' = createInternalName name n
    put $ FreshState (M.insertWith (++) name [name'] m) n' g
    return name'
  popId =
    modify $ \(FreshState m n g) -> FreshState (M.adjust safeTail (head g) m) n (tail g)
  lookupId name = gets $ fmap head . M.lookup name . nameMap

emptyFreshState :: FreshState
emptyFreshState = FreshState { nameMap = M.empty, freshInt = 0, ctx = [] }

--------------------------------------------------------------------------------

uniqify :: Expr a -> Expr a
uniqify expr = evalState (uniqifyExpr expr) emptyFreshState

uniqifyExpr :: (MonadFresh m) => Expr a -> m (Expr a)
uniqifyExpr (Lam bs body l) =
  (Lam <$> mapM uniqifyBind bs <*> uniqifyExpr body <*> pure l)
  <* mapM (const popId) bs
uniqifyExpr (Let bind sig e1 e2 l) =
  (Let <$> uniqifyBind bind <*> uniqifySig sig <*> uniqifyExpr e1 <*> uniqifyExpr e2 <*> pure l)
  <* popId
uniqifyExpr (Id id l) = Id . fromJust <$> lookupId id <*> pure l

uniqifyExpr e@Number{} = pure e
uniqifyExpr e@Boolean{} = pure e
uniqifyExpr e@Unit{} = pure e
uniqifyExpr (Prim2 op e1 e2 l) =
  Prim2 op <$> uniqifyExpr e1 <*> uniqifyExpr e2 <*> pure l
uniqifyExpr (If e1 e2 e3 l) =
  If <$> uniqifyExpr e1 <*> uniqifyExpr e2 <*> uniqifyExpr e3 <*> pure l
uniqifyExpr (Tuple e1 e2 l) =
  Tuple <$> uniqifyExpr e1 <*> uniqifyExpr e2 <*> pure l
uniqifyExpr (GetItem e field l) =
  GetItem <$> uniqifyExpr e <*> pure field <*> pure l
uniqifyExpr (App e1 e2 l) =
  App <$> uniqifyExpr e1 <*> uniqifyExpr e2 <*> pure l

uniqifySig :: (MonadFresh m) => Sig a -> m (Sig a)
uniqifySig Infer = pure Infer
uniqifySig (Check r) = Check <$> uniqifyRPoly r
uniqifySig (Assume r) = Assume <$> uniqifyRPoly r

uniqifyRPoly :: (MonadFresh m) => RPoly Expr a -> m (RPoly Expr a)
uniqifyRPoly (RForall tvars r) =
  (RForall <$> mapM uniqifyBindingTVar tvars <*> uniqifyRType r)
  <* popId

uniqifyRType :: (MonadFresh m) => RType Expr a -> m (RType Expr a)
uniqifyRType (RBase bind typ expr) =
  (RBase <$> uniqifyBind bind <*> uniqifyType typ <*> uniqifyExpr expr)
  <* popId
uniqifyRType (RFun bind rtype1 rtype2) =
  (RFun <$> uniqifyBind bind <*> uniqifyRType rtype1 <*> uniqifyRType rtype2)
  <* popId
uniqifyRType (RRTy bind rtype expr) =
  (RRTy <$> uniqifyBind bind <*> uniqifyRType rtype <*> uniqifyExpr expr)
  <* popId

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

uniqifyBind :: (MonadFresh m) => Bind a -> m (Bind a)
uniqifyBind (Bind name l) = Bind <$> refreshId name <*> pure l

uniqifyBindingTVar :: (MonadFresh m) => TVar -> m TVar
uniqifyBindingTVar (TV name) = TV <$> refreshId name

uniqifyTVar :: (MonadFresh m) => TVar -> m TVar
uniqifyTVar (TV name) = TV <$> (fromJust <$> lookupId name)
