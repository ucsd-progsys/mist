{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}

module Language.Mist.Fresh (
     uniquify,
     refresh,

     varNum,

     FreshT,
     Fresh,
     ) where

import Control.Monad.State
import Control.Monad.Identity (Identity)
import qualified Data.Map.Strict as M
import Data.Maybe (fromJust, fromMaybe)
import Data.List.Split (splitOn)

import Language.Mist.Types
import Language.Mist.Utils (safeTail)

cSEPARATOR = "##"
varNum :: Id -> Int
varNum = read . last . splitOn cSEPARATOR
-- change this if it's too slow
createInternalName name number = head (splitOn cSEPARATOR name) ++ cSEPARATOR ++ show number


--------------------------------------------------------------------------------
-- | A MonadFresh encompasses the operations for generating fresh, scoped names
--------------------------------------------------------------------------------
class Monad m => MonadFresh m where
  refreshId :: Id -> m Id         -- ^ generate a fresh name for the argument
  popId     :: m ()               -- ^ removes the most recent scoped version of a fresh name
  lookupId  :: Id -> m (Maybe Id) -- ^ gets the assigned fresh name

--------------------------------------------------------------------------------
data FreshState = FreshState { nameMap :: M.Map Id [Id], freshInt :: Integer, ctx :: [Id] }
type FreshT = StateT FreshState
type Fresh = FreshT Identity

instance Monad m => MonadFresh (FreshT m) where
  refreshId name = do
    FreshState m n g <- get
    let name' = createInternalName name n
        n' = n + 1
    put $ FreshState (M.insertWith (++) name [name'] m) n' g
    return name'
  popId = modify $ \(FreshState m n g) ->
    FreshState (M.adjust safeTail (head g) m) n (tail g)
  lookupId name = gets $ fmap head . M.lookup name . nameMap

emptyFreshState :: FreshState
emptyFreshState = FreshState { nameMap = M.empty, freshInt = 0, ctx = [] }
--------------------------------------------------------------------------------

uniquify :: Freshable a => a -> a
uniquify expr = evalState (refresh expr) emptyFreshState

class Freshable a where
  refresh :: MonadFresh m => a -> m a

instance Freshable (Expr a) where
  refresh (Lam bs body l) =
    (Lam <$> mapM refresh bs <*> refresh body <*> pure l)
    <* mapM (const popId) bs
  refresh (Let bind sig e1 e2 l) =
    (Let <$> refresh bind <*> refresh sig <*> refresh e1 <*> refresh e2 <*> pure l)
    <* popId
  refresh (Id id l) = Id . fromJust <$> lookupId id <*> pure l

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
  refresh (CLam bs body l) =
    (CLam <$> mapM refresh bs <*> refresh body <*> pure l)
    <* mapM (const popId) bs
  refresh (CLet bind e1 e2 l) =
    (CLet <$> refresh bind <*> refresh e1 <*> refresh e2 <*> pure l)
    <* popId
  refresh (CId id l) = CId . fromJust <$> lookupId id <*> pure l

  refresh e@CNumber{} = pure e
  refresh e@CBoolean{} = pure e
  refresh e@CUnit{} = pure e
  refresh (CPrim2 op e1 e2 l) =
    CPrim2 op <$> refresh e1 <*> refresh e2 <*> pure l
  refresh (CIf e1 e2 e3 l) =
    CIf <$> refresh e1 <*> refresh e2 <*> refresh e3 <*> pure l
  refresh (CTuple e1 e2 l) =
    CTuple <$> refresh e1 <*> refresh e2 <*> pure l
  refresh (CGetItem e field l) =
    CGetItem <$> refresh e <*> pure field <*> pure l
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

instance Freshable (e a) => Freshable (RPoly e a) where
  refresh (RForall tvars r) =
    (RForall <$> mapM uniquifyBindingTVar tvars <*> refresh r)
    <* popId

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

instance Freshable Type where
  refresh (TVar tvar) = TVar <$> uniquifyTVar tvar
  refresh TInt = pure TInt
  refresh TBool = pure TBool
  refresh (domain :=> codomain) =
    (:=>) <$> mapM refresh domain <*> refresh codomain
  refresh (TPair t1 t2) =
    TPair <$> refresh t1 <*> refresh t2
  refresh (TCtor c ts) =
    TCtor c <$> mapM refresh ts

instance Freshable (Bind a) where
  refresh (Bind name l) = Bind <$> refreshId name <*> pure l

instance Freshable (AnnBind a) where
  refresh (AnnBind name t l) = AnnBind <$> refreshId name <*> refresh t <*> pure l


uniquifyBindingTVar :: (MonadFresh m) => TVar -> m TVar
uniquifyBindingTVar (TV name) = TV <$> refreshId name

uniquifyTVar :: (MonadFresh m) => TVar -> m TVar
uniquifyTVar (TV name) = TV <$> (fromMaybe name <$> lookupId name)
