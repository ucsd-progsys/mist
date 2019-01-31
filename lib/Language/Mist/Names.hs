{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE UndecidableInstances #-}

module Language.Mist.Names
  ( uniquify
  , refresh

  , varNum

  , FreshT
  , Fresh
  , FreshState
  , evalFreshT
  , runFresh

  , Subable
  , Subst
  , subst
  , subst1

  , substReftPred
  , substReftPred1
  , substReftType
  , substReftType1
  , substReftReft
  , substReftReft1

  , emptyFreshState
  ) where

import qualified Data.Map.Strict as M
import Data.Maybe (fromMaybe)
import Data.List.Split (splitOn)
import Control.Applicative (Alternative)

import Language.Mist.Types
import Language.Mist.Utils (safeTail)

import Control.Monad.State
import Control.Monad.Writer
import Control.Monad.Identity
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.Cont
import Control.Monad.Fail


cSEPARATOR = "##"
varNum :: Id -> Int
varNum = read . last . splitOn cSEPARATOR
-- change this if it's too slow
createInternalName name number = head (splitOn cSEPARATOR name) ++ cSEPARATOR ++ show number

--------------------------------------------------------------------------------
-- | Substitutions
--------------------------------------------------------------------------------
type Subst e = M.Map Id e

-- | e[ex/x]
subst1 :: Subable e a => e -> Id -> a -> a
subst1 ex x e = subst (M.singleton x ex) e

-- | Substitutes in the predicates of an RType
substReftPred :: (Subable e r) => Subst e -> RType r a -> RType r a
substReftPred = error "TODO"

substReftPred1 :: (Subable e r) => e -> Id -> RType r a -> RType r a
substReftPred1 = error "TODO"

-- | Substitutes in the Types of an RType
substReftType :: (Subable t Type) => Subst t -> RType r a -> RType r a
substReftType = error "TODO"

substReftType1 :: (Subable t Type) => t -> Id -> RType r a -> RType r a
substReftType1 = error "TODO"

-- | Substitutes an RType for an RType
substReftReft :: Subst (RType r a) -> RType r a -> RType r a
substReftReft = error "TODO"

substReftReft1 :: RType r a -> Id -> RType r a -> RType r a
substReftReft1 = error "TODO"

-- instance Subable e r => Subable e (RType r a) where
--   _subst su (RBase bind typ expr) =
--     RBase bind typ (_subst (M.delete (bindId bind) su) expr)
--   _subst su (RFun bind rtype1 rtype2) =
--     RFun bind (_subst su rtype1) (_subst (M.delete (bindId bind) su) rtype2)
--   _subst su (RRTy bind rtype expr) =
--     RRTy bind (_subst su rtype) (_subst (M.delete (bindId bind) su) expr)
--   _subst su (RForall tvars r) =
--     RForall tvars (_subst su r)

-- instance Subable Type (RType r a) where
--   _subst su (RBase bind typ p) =
--     RBase bind (_subst su typ) p
--   _subst su (RFun bind rtype1 rtype2) =
--     RFun bind (_subst su rtype1) (_subst su rtype2)
--   _subst su (RRTy bind rtype expr) =
--     RRTy bind (_subst su rtype) expr
--   _subst su (RForall tvar r) =
--     RForall tvar (_subst (M.delete (unTV tvar) su) r)

-- instance Subable (RType r a) (RType r a) where
--   _subst su (RBase bind typ expr) =
--     case flip M.lookup su =<< tvar typ of
--         Nothing -> RBase bind typ expr
--         Just rt -> RRTy bind rt expr
--   _subst su (RFun bind rtype1 rtype2) =
--     RFun bind (_subst su rtype1) (_subst su rtype2)
-- -- the types of refinements don't matter, expect that we check that they're
-- -- Bool, hopefully before we get here.
--   _subst su (RRTy bind rtype expr) =
--     RRTy bind (_subst su rtype) expr
--   _subst su (RForall tvar r) =
--     RForall tvar (_subst (M.delete (unTV tvar) su) r)


subst :: Subable a b => Subst a -> b -> b
subst su e
    | M.null su = e
subst su e = _subst su e

-- TODO: clarify if this is a parallel substitution
-- | substitutes an e in a
class Subable e a where
  _subst :: Subst e -> a -> a

-- instance Subable e a => Subable e [a] where
--   _subst su = fmap (_subst su)
instance Subable Type [Type] where
  _subst su = fmap (_subst su)

instance Subable Type (ElaboratedType r a) where
  _subst su (Left rType) = Left $ substReftType su rType
  _subst su (Right typ) = Right $ _subst su typ

instance Subable Type t => Subable Type (Expr t a) where
  _subst _su e@Number{} = e
  _subst _su e@Boolean{} = e
  _subst _su e@Unit{} = e
  _subst _su e@Id{} = e
  _subst su (Prim2 op e1 e2 l)
    = Prim2 op (_subst su e1) (_subst su e2) l
  _subst su (If e e1 e2 l)
    = If (_subst su e) (_subst su e1) (_subst su e2) l
  _subst su (Let bind e1 e2 l)
    = Let (_subst su bind) (_subst su e1) (_subst su e2) l
  _subst su (App e1 e2 l)
    = App (_subst su e1) (_subst su e2) l
  _subst su (Lam bind e l)
    = Lam (_subst su bind) (_subst su e) l
  _subst su (TApp e typ l)
    = TApp (_subst su e) (_subst su typ) l
  _subst su (TAbs tvar e l)
    = TAbs tvar (_subst (M.delete (unTV tvar) su) e) l

instance Subable Type Type where
  _subst su t@(TVar (TV a)) = fromMaybe t $ M.lookup a su

  _subst _ TUnit = TUnit
  _subst _ TInt  = TInt
  _subst _ TBool = TBool

  _subst su (t1 :=> t2) = _subst su t1 :=> _subst su t2
  _subst su (TCtor c t2) = TCtor c (_subst su t2)
  _subst su (TForall tvar t) = TForall tvar (_subst (M.delete (unTV tvar) su) t)

instance Subable Type t => Subable Type (AnnBind t a) where
  _subst su (AnnBind name t l) = AnnBind name (_subst su t) l

instance Predicate r => Subable Id r where
  _subst su r = M.foldrWithKey (\x y r' -> varSubst x y r') r su




--------------------------------------------------------------------------------
data FreshState = FreshState { nameMap :: M.Map Id [Id], freshInt :: Integer, ctx :: [Id] }

newtype FreshT m a = FreshT { unFreshT :: StateT FreshState m a }
  deriving (Functor, Applicative, Alternative, Monad, MonadPlus, MonadTrans,
            MonadError e, MonadReader r, MonadWriter w, MonadFix, MonadFail, MonadIO, MonadCont)

instance MonadState s m => MonadState s (FreshT m) where
  get = lift get
  put = lift . put
  state = lift . state

type Fresh = FreshT Identity

instance Monad m => MonadFresh (FreshT m) where
  refreshId name = do
    FreshState m n g <- FreshT get
    let name' = createInternalName name n
        n' = n + 1
    FreshT (put $ FreshState (M.insertWith (++) name [name'] m) n' g)
    return name'
  popId = FreshT (modify $ \(FreshState m n g) ->
    FreshState (M.adjust safeTail (head g) m) n (tail g))
  lookupId name = FreshT (gets $ fmap head . M.lookup name . nameMap)

emptyFreshState :: FreshState
emptyFreshState = FreshState { nameMap = M.empty, freshInt = 0, ctx = [] }

evalFreshT :: Monad m => FreshT m a -> FreshState -> m a
evalFreshT freshT initialNames = evalStateT (unFreshT freshT) initialNames

runFresh :: Fresh a -> a
runFresh m = runIdentity $ evalFreshT m emptyFreshState
--------------------------------------------------------------------------------

uniquify :: Freshable a => a -> a
uniquify = runFresh . refresh

class Freshable a where
  refresh :: MonadFresh m => a -> m a

instance (Freshable t) => Freshable (Expr t a) where
  refresh (Lam b body l) =
    (Lam <$> refresh b <*> refresh body <*> pure l)
    <* (const popId) b
  refresh (Let bind e1 e2 l) =
    (Let <$> refresh bind <*> refresh e1 <*> refresh e2 <*> pure l)
    <* popId
  refresh (Id id l) = Id . fromMaybe id <$> lookupId id <*> pure l

  refresh e@Number{} = pure e
  refresh e@Boolean{} = pure e
  refresh e@Unit{} = pure e
  refresh (Prim2 op e1 e2 l) =
    Prim2 op <$> refresh e1 <*> refresh e2 <*> pure l
  refresh (If e1 e2 e3 l) =
    If <$> refresh e1 <*> refresh e2 <*> refresh e3 <*> pure l
  refresh (App e1 e2 l) =
    App <$> refresh e1 <*> refresh e2 <*> pure l
  refresh (TApp e t l) =
    TApp <$> refresh e <*> refresh t <*> pure l
  refresh (TAbs tvar e l) = do
    TAbs <$> uniquifyTVar tvar <*> refresh e <*> pure l
    <* popId

instance Freshable e => Freshable (RType e a) where
  refresh (RBase bind typ expr) =
    (RBase <$> refresh bind <*> refresh typ <*> refresh expr)
    <* popId
  refresh (RFun bind rtype1 rtype2) =
    (RFun <$> refresh bind <*> refresh rtype1 <*> refresh rtype2)
    <* popId
  refresh (RRTy bind rtype expr) =
    (RRTy <$> refresh bind <*> refresh rtype <*> refresh expr)
    <* popId
  refresh (RForall tvar r) =
    (RForall <$> uniquifyBindingTVar tvar <*> refresh r)
    <* (const popId) tvar
  refresh (RTVar alpha) =
    RTVar <$> uniquifyTVar alpha

instance Freshable Type where
  refresh (TVar tvar) = TVar <$> uniquifyTVar tvar
  refresh TInt = pure TInt
  refresh TBool = pure TBool
  refresh TUnit = pure TUnit
  refresh (domain :=> codomain) =
    (:=>) <$> refresh domain <*> refresh codomain
  refresh (TCtor c ts) =
    TCtor c <$> mapM refresh ts
  refresh (TForall tvar t) =
    TForall <$> uniquifyBindingTVar tvar <*> refresh t
    <* (const popId) tvar

instance Freshable (Bind a) where
  refresh (Bind name l) = Bind <$> refreshId name <*> pure l

instance Freshable t => Freshable (AnnBind t a) where
  refresh (AnnBind name t l) = AnnBind <$> refreshId name <*> refresh t <*> pure l


uniquifyBindingTVar :: (MonadFresh m) => TVar -> m TVar
uniquifyBindingTVar (TV name) = TV <$> refreshId name

uniquifyTVar :: (MonadFresh m) => TVar -> m TVar
uniquifyTVar (TV name) = TV <$> (fromMaybe name <$> lookupId name)
