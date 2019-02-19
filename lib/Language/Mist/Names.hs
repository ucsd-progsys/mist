{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE LambdaCase #-}

module Language.Mist.Names
  (
    uniquify

  , cSEPARATOR


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

  , Uniqable
  ) where

import qualified Data.Map.Strict as M
import Data.Maybe (fromMaybe, fromJust)
import Data.List.Split (splitOn)
import Control.Applicative (Alternative)

import Language.Mist.Types

import Control.Monad.State
import Control.Monad.Writer
import Control.Monad.Identity
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.Cont
import Control.Monad.Fail

-- TODO: make this a part of refresh somehow
-- TODO: this needs to be fixed
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
substReftPred su (RBase bind typ expr) =
  RBase bind typ (subst (M.delete (bindId bind) su) expr)
substReftPred su (RFun bind rtype1 rtype2) =
  RFun bind (substReftPred su rtype1) (substReftPred (M.delete (bindId bind) su) rtype2)
substReftPred su (RRTy bind rtype expr) =
  RRTy bind (substReftPred su rtype) (subst (M.delete (bindId bind) su) expr)
substReftPred su (RForall tvars r) =
  RForall tvars (substReftPred su r)

substReftPred1 :: (Subable e r) => e -> Id -> RType r a -> RType r a
substReftPred1 e x rtype = substReftPred (M.singleton x e) rtype

-- | Substitutes in the Types of an RType
substReftType :: (Subable t Type) => Subst t -> RType r a -> RType r a
substReftType su (RBase bind typ p) =
  RBase bind (subst su typ) p
substReftType su (RFun bind rtype1 rtype2) =
  RFun bind (substReftType su rtype1) (substReftType su rtype2)
substReftType su (RRTy bind rtype expr) =
  RRTy bind (substReftType su rtype) expr
substReftType su (RForall tvar r) =
  RForall tvar (substReftType (M.delete (unTV tvar) su) r)

substReftType1 :: (Subable t Type) => t -> Id -> RType r a -> RType r a
substReftType1 t x rtype = substReftType (M.singleton x t) rtype

-- | Substitutes an RType for an RType
substReftReft :: Subst (RType r a) -> RType r a -> RType r a
substReftReft su (RBase bind typ expr) =
  case flip M.lookup su =<< toTVar typ of
      Nothing -> RBase bind typ expr
      Just rt -> RRTy bind rt expr
substReftReft su (RFun bind rtype1 rtype2) =
  RFun bind (substReftReft su rtype1) (substReftReft su rtype2)
substReftReft su (RRTy bind rtype expr) =
  RRTy bind (substReftReft su rtype) expr
substReftReft su (RForall tvar r) =
  RForall tvar (substReftReft (M.delete (unTV tvar) su) r)

substReftReft1 :: RType r a -> Id -> RType r a -> RType r a
substReftReft1 rtype1 x rtype2 = substReftReft (M.singleton x rtype1) rtype2

toTVar :: Type -> Maybe Id
toTVar (TVar (TV t)) = Just t
toTVar _ = Nothing

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
data FreshState = FreshState { freshInt :: Integer }

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
    FreshState n <- FreshT get
    let name' = createInternalName name n
        n' = n + 1
    FreshT (put $ FreshState n')
    return name'
  -- popId = FreshT (modify $ \(FreshState m n g) ->
  --   FreshState (M.adjust safeTail (head g) m) n (tail g))
  -- lookupId name = FreshT (gets $ fmap head . M.lookup name . nameMap)

emptyFreshState :: FreshState
emptyFreshState = FreshState { freshInt = 0 }

evalFreshT :: Monad m => FreshT m a -> FreshState -> m a
evalFreshT freshT initialNames = evalStateT (unFreshT freshT) initialNames

runFresh :: Fresh a -> a
runFresh m = runIdentity $ evalFreshT m emptyFreshState
--------------------------------------------------------------------------------

uniquify :: Uniqable a => a -> a
uniquify e = runFresh $ evalStateT (unique e) emptyNameEnv

type UniqableContext = StateT NameEnv Fresh

type NameEnv = M.Map Id [Id]
emptyNameEnv = M.empty

pushNewName :: Id -> Id -> NameEnv -> NameEnv
pushNewName x x' env = M.alter (\case
                                   Nothing -> Just [x']
                                   (Just xs) -> Just (x':xs)) x env

-- | removes the innermost bound new name for an identifier
popNewName :: Id -> NameEnv -> NameEnv
popNewName x env = M.adjust tail x env

-- | looks up the innermost bound new name for an identifier
lookupNewName :: Id -> NameEnv -> Maybe Id
lookupNewName x env = fmap head $ M.lookup x env

class Uniqable a where
  unique :: a -> UniqableContext a

instance (Uniqable t) => Uniqable (Expr t a) where
  unique (Lam b body l) = do
    b' <- unique b
    body' <- unique body
    modify $ popNewName (bindId b)
    pure $ Lam b' body' l
  unique (Let bind e1 e2 l) = do
    bind' <- unique bind
    e1' <- unique e1
    e2' <- unique e2
    modify $ popNewName (bindId bind)
    pure $ Let bind' e1' e2' l
  unique (Id id l) = Id . fromJust <$> gets (lookupNewName id) <*> pure l

  unique e@Number{} = pure e
  unique e@Boolean{} = pure e
  unique e@Unit{} = pure e
  unique (Prim2 op e1 e2 l) =
    Prim2 op <$> unique e1 <*> unique e2 <*> pure l
  unique (If e1 e2 e3 l) =
    If <$> unique e1 <*> unique e2 <*> unique e3 <*> pure l
  unique (App e1 e2 l) =
    App <$> unique e1 <*> unique e2 <*> pure l
  unique (TApp e t l) =
    TApp <$> unique e <*> unique t <*> pure l
  unique (TAbs tvar e l) = do
    tvar' <- uniquifyBindingTVar tvar
    e' <- unique e
    modify $ popNewName (unTV tvar)
    pure $ TAbs tvar' e' l

instance Uniqable e => Uniqable (RType e a) where
  unique (RBase bind typ expr) = do
    bind' <- unique bind
    typ' <- unique typ
    expr' <- unique expr
    modify $ popNewName (bindId bind)
    pure $ RBase bind' typ' expr'
  unique (RFun bind rtype1 rtype2) = do
    bind' <- unique bind
    rtype1' <- unique rtype1
    rtype2' <- unique rtype2
    modify $ popNewName (bindId bind)
    pure $ RFun bind' rtype1' rtype2'
  unique (RRTy bind rtype expr) = do
    bind' <- unique bind
    rtype' <- unique rtype
    expr' <- unique expr
    modify $ popNewName (bindId bind)
    pure $ RRTy bind' rtype' expr'
  unique (RForall tvar rtype) = do
    tvar' <- uniquifyBindingTVar tvar
    rtype' <- unique rtype
    modify $ popNewName (unTV tvar)
    pure $ RForall tvar' rtype'

instance Uniqable Type where
  unique (TVar tvar) = TVar <$> uniquifyTVar tvar
  unique TInt = pure TInt
  unique TBool = pure TBool
  unique TUnit = pure TUnit
  unique (domain :=> codomain) =
    (:=>) <$> unique domain <*> unique codomain
  unique (TCtor c ts) =
    TCtor c <$> mapM unique ts
  unique (TForall tvar t) = do
    tvar' <- uniquifyBindingTVar tvar
    t' <- unique t
    modify $ popNewName (unTV tvar)
    pure $ TForall tvar' t'

instance Uniqable r => Uniqable (ParsedType r a) where
  unique (ParsedCheck rtype) = ParsedCheck <$> unique rtype
  unique (ParsedAssume rtype) = ParsedAssume <$> unique rtype
  unique ParsedInfer = pure ParsedInfer

instance Uniqable () where
  unique _ = pure ()

instance Uniqable (Bind a) where
  unique (Bind name l) = do
    name' <- refreshId name
    modify $ pushNewName name name'
    pure $ Bind name' l

instance Uniqable t => Uniqable (AnnBind t a) where
  unique (AnnBind name t l) = do
    name' <- refreshId name
    t' <- unique t
    modify $ pushNewName name name'
    pure $ AnnBind name' t' l

uniquifyBindingTVar :: TVar -> UniqableContext TVar
uniquifyBindingTVar (TV name) = do
  name' <- refreshId name
  modify $ pushNewName name name'
  pure $ TV name'

uniquifyTVar :: TVar -> UniqableContext TVar
uniquifyTVar (TV name) = TV . fromJust <$> gets (lookupNewName name)
