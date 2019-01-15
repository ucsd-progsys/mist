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

  , MonadFresh (..)
  , FreshT
  , Fresh
  , evalFreshT
  , runFresh

  , Subable (..)
  , subst1
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

-- | substitutes an e in a
class Subable e a where
  subst :: Subst e -> a -> a

--- subst values for value-space variables
instance Subable (Core a) (Core a) where
  subst su e
    | M.null su = e
  subst su e@(CId id _) = fromMaybe e $ M.lookup id su

  subst su (CLam b body l) =
    CLam (subst su b) (subst (M.delete (aBindId b) su) body) l
  subst su (CLet bind e1 e2 l) =
    CLet (subst su bind) (subst su e1) (subst (M.delete (aBindId bind) su) e2) l

  subst _  e@CNumber{} = e
  subst _  e@CBoolean{} = e
  subst _  e@CUnit{} = e
  subst _  e@CPrim{} = e
  subst su (CPrim2 op e1 e2 l) =
    CPrim2 op (subst su e1)(subst su e2) l
  subst su (CIf e1 e2 e3 l) =
    CIf (subst su e1) (subst su e2) (subst su e3) l
  subst su (CTuple e1 e2 l) =
    CTuple (subst su e1)(subst su e2) l
  subst su (CApp e1 e2 l) =
    CApp (subst su e1) (subst su e2) l
  subst su (CTApp e t l) =
    CTApp (subst su e) t l
  subst su (CTAbs tvs e l) =
    CTAbs tvs (subst su e) l

instance Subable (Core a) (AnnBind a) where
  subst su (AnnBind name t l) = AnnBind name (subst su t) l

instance Subable e a => Subable e [a] where
  subst su = fmap (subst su)

instance Subable (e a) (e a) => Subable (e a) (RType e a) where
  subst su (RBase bind typ expr) =
    RBase bind typ (subst (M.delete (bindId bind) su) expr)
  subst su (RFun bind rtype1 rtype2) =
    RFun bind (subst su rtype1) (subst (M.delete (bindId bind) su) rtype2)
  subst su (RRTy bind rtype expr) =
    RRTy bind (subst su rtype) (subst (M.delete (bindId bind) su) expr)
  subst su (RForall tvars r) =
    RForall tvars (subst su r)

--- subst types for tyvars
instance Subable Type Type where
  subst su t@(TVar (TV a)) = fromMaybe t $ M.lookup a su

  subst _ TUnit = TUnit
  subst _ TInt  = TInt
  subst _ TBool = TBool

  subst su (t1 :=> t2) = subst su t1 :=> subst su t2
  subst su (TPair t1 t2) = TPair (subst su t1) (subst su t2)
  subst su (TCtor c t2) = TCtor c (subst su t2)
  subst su (TForall tvar t) = TForall tvar (subst (M.delete (unTV tvar) su) t)

instance Subable Type (Core a) where
  subst su e
    | M.null su = e

  subst su (CTApp e t l) =
    CTApp (subst su e) (subst su t) l
  subst su (CTAbs tv e l) =
    CTAbs tv (subst (M.delete (unTV tv) su) e) l
  subst su (CLet bind e1 e2 l) =
    CLet (subst su bind) (subst su e1) (subst su e2) l
  subst su (CLam bs body l) =
    CLam (subst su bs) (subst su body) l

  subst _ e = e

instance Subable Type (AnnBind a) where
  subst su (AnnBind name t l) = AnnBind name (subst su t) l

unTV :: TVar -> Id
unTV (TV t) = t

instance Subable Type (e a) => Subable Type (RType e a) where
  subst su (RBase bind typ p) =
    RBase bind (subst su typ) p
  subst su (RFun bind rtype1 rtype2) =
    RFun bind (subst su rtype1) (subst su rtype2)
  subst su (RRTy bind rtype expr) =
    RRTy bind (subst su rtype) (subst su expr)
  subst su (RForall tvar r) =
    RForall tvar (subst (M.delete (unTV tvar) su) r)

-- TODO Subst for Exprs

--------------------------------------------------------------------------------
-- | A MonadFresh encompasses the operations for generating fresh, scoped names
--------------------------------------------------------------------------------
class Monad m => MonadFresh m where
  refreshId :: Id -> m Id         -- ^ generate a fresh name for the argument
  popId     :: m ()               -- ^ removes the most recent scoped version of a fresh name
  lookupId  :: Id -> m (Maybe Id) -- ^ gets the assigned fresh name

--------------------------------------------------------------------------------
data FreshState = FreshState { nameMap :: M.Map Id [Id], freshInt :: Integer, ctx :: [Id] }

newtype FreshT m a = FreshT { unFreshT :: StateT FreshState m a }
  deriving (Functor, Applicative, Alternative, Monad, MonadPlus, MonadTrans,
            MonadError e, MonadReader r, MonadWriter w, MonadFix, MonadFail, MonadIO, MonadCont)

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

instance Freshable (Expr a) where
  refresh (Lam b body l) =
    (Lam <$> refresh b <*> refresh body <*> pure l)
    <* (const popId) b
  refresh (Let bind sig e1 e2 l) =
    (Let <$> refresh bind <*> refresh sig <*> refresh e1 <*> refresh e2 <*> pure l)
    <* popId
  refresh (Id id l) = Id . fromMaybe id <$> lookupId id <*> pure l

  refresh e@Number{} = pure e
  refresh e@Boolean{} = pure e
  refresh e@Unit{} = pure e
  refresh (Prim2 op e1 e2 l) =
    Prim2 op <$> refresh e1 <*> refresh e2 <*> pure l
  refresh (If e1 e2 e3 l) =
    If <$> refresh e1 <*> refresh e2 <*> refresh e3 <*> pure l
  refresh (Tuple e1 e2 l) =
    Tuple <$> refresh e1 <*> refresh e2 <*> pure l
  refresh (GetItem e field l) =
    GetItem <$> refresh e <*> pure field <*> pure l
  refresh (App e1 e2 l) =
    App <$> refresh e1 <*> refresh e2 <*> pure l

instance Freshable (Core a) where
  refresh (CLam b body l) =
    (CLam <$> refresh b <*> refresh body <*> pure l)
    <* (const popId) b
  refresh (CLet bind e1 e2 l) =
    (CLet <$> refresh bind <*> refresh e1 <*> refresh e2 <*> pure l)
    <* popId
  refresh (CId id l) = CId . fromMaybe id <$> lookupId id <*> pure l

  refresh e@CNumber{} = pure e
  refresh e@CBoolean{} = pure e
  refresh e@CUnit{} = pure e
  refresh (CPrim2 op e1 e2 l) =
    CPrim2 op <$> refresh e1 <*> refresh e2 <*> pure l
  refresh (CIf e1 e2 e3 l) =
    CIf <$> refresh e1 <*> refresh e2 <*> refresh e3 <*> pure l
  refresh (CTuple e1 e2 l) =
    CTuple <$> refresh e1 <*> refresh e2 <*> pure l
  refresh e@CPrim{} = pure e
  refresh (CApp e1 e2 l) =
    CApp <$> refresh e1 <*> refresh e2 <*> pure l
  refresh (CTApp e t l) =
    CTApp <$> refresh e <*> pure t <*> pure l
  refresh (CTAbs tvs e l) =
    CTAbs tvs <$> refresh e <*> pure l

instance Freshable (Sig a) where
  refresh Infer = pure Infer
  refresh (Check r) = Check <$> refresh r
  refresh (Assume r) = Assume <$> refresh r

instance Freshable (e a) => Freshable (RType e a) where
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

instance Freshable Type where
  refresh (TVar tvar) = TVar <$> uniquifyTVar tvar
  refresh TInt = pure TInt
  refresh TBool = pure TBool
  refresh TUnit = pure TUnit
  refresh (domain :=> codomain) =
    (:=>) <$> refresh domain <*> refresh codomain
  refresh (TPair t1 t2) =
    TPair <$> refresh t1 <*> refresh t2
  refresh (TCtor c ts) =
    TCtor c <$> mapM refresh ts
  refresh (TForall tvar t) =
    TForall <$> uniquifyBindingTVar tvar <*> refresh t
    <* (const popId) tvar

instance Freshable (Bind a) where
  refresh (Bind name l) = Bind <$> refreshId name <*> pure l

instance Freshable (AnnBind a) where
  refresh (AnnBind name t l) = AnnBind <$> refreshId name <*> refresh t <*> pure l


uniquifyBindingTVar :: (MonadFresh m) => TVar -> m TVar
uniquifyBindingTVar (TV name) = TV <$> refreshId name

uniquifyTVar :: (MonadFresh m) => TVar -> m TVar
uniquifyTVar (TV name) = TV <$> (fromMaybe name <$> lookupId name)


-------------------------------------------------------------------------------
-- MonadFresh instances -------------------------------------------------------
-------------------------------------------------------------------------------

instance MonadState s m => MonadState s (FreshT m) where
  get = lift get
  put = lift . put
  state = lift . state

instance (Monoid w, MonadFresh m) => MonadFresh (WriterT w m) where
  refreshId = lift . refreshId
  popId = lift popId
  lookupId = lift . lookupId

instance MonadFresh m => MonadFresh (IdentityT m) where
  refreshId = lift . refreshId
  popId = lift popId
  lookupId = lift . lookupId

instance MonadFresh m => MonadFresh (ExceptT e m) where
  refreshId = lift . refreshId
  popId = lift popId
  lookupId = lift . lookupId

instance MonadFresh m => MonadFresh (StateT s m) where
  refreshId = lift . refreshId
  popId = lift popId
  lookupId = lift . lookupId

instance MonadFresh m => MonadFresh (ReaderT r m) where
  refreshId = lift . refreshId
  popId = lift popId
  lookupId = lift . lookupId

instance MonadFresh m => MonadFresh (ContT r m) where
  refreshId = lift . refreshId
  popId = lift popId
  lookupId = lift . lookupId
