{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}

module Language.Mist.Names
  (
    uniquify

  , cSEPARATOR

  , varNum
  , varHead

  , FreshT
  , Fresh
  , FreshState
  , evalFreshT
  , runFresh

  , (|->)
  , Subable
  , subst

  , substReftPred
  , substReftType
  , substReftReft

  , emptyFreshState

  , Uniqable
  ) where

import qualified Data.Map.Strict as M
import Data.Maybe (fromMaybe)
import Data.List.Split (splitOn)
import Data.Foldable (traverse_)
import Control.Applicative (Alternative)

import Language.Mist.Types
import Language.Mist.Utils

import Control.Arrow (second)
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
varHead :: Id -> Id
varHead = head . splitOn cSEPARATOR
-- change this if it's too slow
createInternalName name number = head (splitOn cSEPARATOR name) ++ cSEPARATOR ++ show number

(|->) :: Id -> e -> Subst e
x |-> e = M.singleton x e

fromJustOrErr e = fromMaybe $ error $ "Unbound identifer: " ++ show e

--------------------------------------------------------------------------------
-- | Substitutions
--------------------------------------------------------------------------------
-- | Substitutes in the predicates of an RType
substReftPred :: (Subable e r) => Subst e -> RType r a -> RType r a
substReftPred su (RApp c ts) =
  RApp c $ second (substReftPred su) <$> ts
substReftPred su (RBase bind typ expr) =
  RBase bind typ (subst (M.delete (bindId bind) su) expr)
substReftPred su (RIFun bind rtype1 rtype2) =
  RIFun bind (substReftPred su rtype1) (substReftPred (M.delete (bindId bind) su) rtype2)
substReftPred su (RFun bind rtype1 rtype2) =
  RFun bind (substReftPred su rtype1) (substReftPred (M.delete (bindId bind) su) rtype2)
substReftPred su (RRTy bind rtype expr) =
  RRTy bind (substReftPred su rtype) (subst (M.delete (bindId bind) su) expr)
substReftPred su (RForall tvars r) =
  RForall tvars (substReftPred su r)
substReftPred su (RForallP tvars r) =
  RForallP tvars (substReftPred su r)

-- | Substitutes in the Types of an RType
substReftType :: (Subable t Type) => Subst t -> RType r a -> RType r a
substReftType su (RBase bind typ p) =
  RBase bind (subst su typ) p
substReftType su (RFun bind rtype1 rtype2) =
  RFun bind (substReftType su rtype1) (substReftType su rtype2)
substReftType su (RIFun bind rtype1 rtype2) =
  RIFun bind (substReftType su rtype1) (substReftType su rtype2)
substReftType su (RApp c ts) =
  RApp c $ second (substReftType su) <$> ts
substReftType su (RRTy bind rtype expr) =
  RRTy bind (substReftType su rtype) expr
substReftType su (RForall tvar r) =
  RForall tvar (substReftType (M.delete (unTV tvar) su) r)
substReftType su (RForallP tvar r) =
  RForallP tvar (substReftType (M.delete (unTV tvar) su) r)

-- | Substitutes an RType for an RType
substReftReft :: Subst (RType r a) -> RType r a -> RType r a
substReftReft su (RBase bind typ expr) = -- TODO: handle polymorphism more appropriately
  case flip M.lookup su =<< toTVar typ of
      Nothing -> RBase bind typ expr
      Just rt -> RRTy bind rt expr
substReftReft su (RFun bind rtype1 rtype2) =
  RFun bind (substReftReft su rtype1) (substReftReft su rtype2)
substReftReft su (RIFun bind rtype1 rtype2) =
  RIFun bind (substReftReft su rtype1) (substReftReft su rtype2)
substReftReft su (RApp c ts) =
  RApp c $ second (substReftReft su) <$> ts
substReftReft su (RRTy bind rtype expr) =
  RRTy bind (substReftReft su rtype) expr
substReftReft su (RForall tvar r) =
  RForall tvar (substReftReft (M.delete (unTV tvar) su) r)
substReftReft su (RForallP tvar r) =
  RForallP tvar (substReftReft (M.delete (unTV tvar) su) r)

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

instance Subable Type (ElaboratedAnnotation r a) where
  _subst su (ElabRefined rType) = ElabRefined $ substReftType su rType
  _subst su (ElabAssume rType) = ElabAssume $ substReftType su rType
  _subst su (ElabUnrefined typ) = ElabUnrefined $ _subst su typ

instance Subable Type t => Subable Type (Expr t a) where
  _subst su (AnnNumber n tag l) = AnnNumber n (_subst su tag) l
  _subst su (AnnBoolean b tag l) = AnnBoolean b (_subst su tag) l
  _subst su (AnnUnit tag l) = AnnUnit (_subst su tag) l
  _subst su (AnnId var tag l) = AnnId var (_subst su tag) l
  _subst su (AnnPrim op tag l) = AnnPrim op (_subst su tag) l
  _subst su (AnnIf e1 e2 e3 tag l) = AnnIf (_subst su e1) (_subst su e2) (_subst su e3) (_subst su tag) l
  _subst su (AnnLet x e1 e2 tag l) = AnnLet (_subst su x) (_subst su e1) (_subst su e2) (_subst su tag) l
  _subst su (AnnApp e1 e2 tag l) = AnnApp (_subst su e1) (_subst su e2) (_subst su tag) l
  _subst su (AnnLam x e tag l) = AnnLam (_subst su x) (_subst su e) (_subst su tag) l
  _subst su (AnnTApp e typ tag l) = AnnTApp (_subst su e) (_subst su typ) (_subst su tag) l
  _subst su (AnnTAbs tvar e tag l) = AnnTAbs tvar (_subst su' e) (_subst su tag) l
    where su' = M.delete (unTV tvar) su

instance Subable Type Type where
  _subst su t@(TVar (TV a)) = fromMaybe t $ M.lookup a su

  _subst _ TUnit = TUnit
  _subst _ TInt  = TInt
  _subst _ TBool = TBool

  _subst su (t1 :=> t2) = _subst su t1 :=> _subst su t2
  _subst su (TCtor c t2) = TCtor c (second (_subst su) <$> t2)
  _subst su (TForall tvar t) = TForall tvar (_subst (M.delete (unTV tvar) su) t)

instance Subable Type t => Subable Type (Bind t a) where
  _subst su (AnnBind name tag l) = AnnBind name (_subst su tag) l

instance Subable (Expr t a) (Expr t a) where
  _subst _ e@AnnNumber{} = e
  _subst _ e@AnnBoolean{} = e
  _subst _ e@AnnUnit{} = e
  _subst su e@(AnnId x _ _) = fromMaybe e $ M.lookup x su
  _subst _su e@AnnPrim{} = e
  _subst su (AnnIf e1 e2 e3 tag l) = AnnIf (_subst su e1) (_subst su e2) (_subst su e3) tag l
  _subst su (AnnLet b e1 e2 tag l) = AnnLet b (_subst su' e1) (_subst su' e2) tag l
    where su' = M.delete (bindId b) su
  _subst su (AnnApp e1 e2 tag l) = AnnApp (_subst su e1) (_subst su e2) tag l
  _subst su (AnnLam b e tag l) = AnnLam b (_subst su' e) tag l
    where su' = M.delete (bindId b) su
  _subst su (AnnTApp e typ tag l) = AnnTApp (_subst su e) typ tag l
  _subst su (AnnTAbs alpha e tag l) = AnnTAbs alpha (_subst su e) tag l

instance Subable Type a => Subable Type (Maybe a) where
  _subst su = fmap (_subst su)

instance (Eq r, Show r, Predicate r) => Subable Id r where
  _subst su r = varSubst su r

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
  -- popAnnId = FreshT (modify $ \(FreshState m n g) ->
  --   FreshState (M.adjust safeTail (head g) m) n (tail g))
  -- lookupAnnId name = FreshT (gets $ fmap head . M.lookup name . nameMap)

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
lookupNewName x env = fmap (safeHead $ error ("unknown name: " ++ x)) $ M.lookup x env

class Uniqable a where
  unique :: a -> UniqableContext a

instance (Uniqable a) => Uniqable (Measures, a) where
  unique (measures, x) = do
    let (names, typs) = unzip $ M.toList measures
    names' <- traverse renameMeasure names
    let measures' = M.fromList $ zip names' typs
    x' <- unique x
    traverse_ (\name -> modify $ popNewName name) names
    pure (measures', x')

    where
      renameMeasure name = do
        name' <- refreshId name
        modify $ pushNewName name name'
        pure $ name'

instance Uniqable (ParsedExpr a) where
  unique (ParsedExpr e) = ParsedExpr <$> unique e

instance (Uniqable t) => Uniqable (Expr t a) where
  unique (AnnLam b body tag l) = do
    tag' <- unique tag
    b' <- unique b
    body' <- unique body
    modify $ popNewName (bindId b)
    pure $ AnnLam b' body' tag' l
  unique (AnnLet bind e1 e2 tag l) = do
    tag' <- unique tag
    bind' <- unique bind
    e1' <- unique e1
    e2' <- unique e2
    modify $ popNewName (bindId bind)
    pure $ AnnLet bind' e1' e2' tag' l
  unique (AnnId id tag l) = AnnId . fromJustOrErr id <$> gets (lookupNewName id) <*> unique tag <*> pure l

  unique (AnnNumber n tag l) = AnnNumber n <$> unique tag <*> pure l
  unique (AnnBoolean b tag l) = AnnBoolean b <$> unique tag <*> pure l
  unique (AnnUnit tag l) = AnnUnit <$> unique tag <*> pure l
  unique (AnnPrim op tag l) = AnnPrim op <$> unique tag <*> pure l
  unique (AnnIf e1 e2 e3 tag l) =
    AnnIf <$> unique e1 <*> unique e2 <*> unique e3 <*> unique tag <*> pure l
  unique (AnnApp e1 e2 tag l) =
    AnnApp <$> unique e1 <*> unique e2 <*> unique tag <*> pure l
  unique (AnnTApp e t tag l) =
    AnnTApp <$> unique e <*> unique t <*> unique tag <*> pure l
  unique (AnnTAbs tvar e tag l) = do
    tag' <- unique tag
    tvar' <- uniquifyBindingTVar tvar
    e' <- unique e
    modify $ popNewName (unTV tvar)
    pure $ AnnTAbs tvar' e' tag' l

instance Uniqable a => Uniqable (Maybe a) where
  unique (Just a) = Just <$> unique a
  unique Nothing = pure Nothing

instance (Uniqable r) => Uniqable (RType r a) where
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
  unique (RIFun bind rtype1 rtype2) = do
    bind' <- unique bind
    rtype1' <- unique rtype1
    rtype2' <- unique rtype2
    modify $ popNewName (bindId bind)
    pure $ RIFun bind' rtype1' rtype2'
  unique (RApp c rts) = RApp c <$> mapM (mapM unique) rts
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
  unique (RForallP tvar rtype) = do
    tvar' <- uniquifyBindingTVar tvar
    rtype' <- unique rtype
    modify $ popNewName (unTV tvar)
    pure $ RForallP tvar' rtype'

instance Uniqable Type where
  unique (TVar tvar) = TVar <$> uniquifyTVar tvar
  unique TInt = pure TInt
  unique TBool = pure TBool
  unique TUnit = pure TUnit
  unique (domain :=> codomain) =
    (:=>) <$> unique domain <*> unique codomain
  unique (TCtor c ts) =
    TCtor c <$> mapM (sequence . second unique) ts
  unique (TForall tvar t) = do
    tvar' <- uniquifyBindingTVar tvar
    t' <- unique t
    modify $ popNewName (unTV tvar)
    pure $ TForall tvar' t'

instance (Uniqable r) => Uniqable (ParsedAnnotation r a) where
  unique (ParsedCheck rtype) = ParsedCheck <$> unique rtype
  unique (ParsedAssume rtype) = ParsedAssume <$> unique rtype
  unique ParsedInfer = pure ParsedInfer

instance Uniqable () where
  unique _ = pure ()

instance Uniqable t => Uniqable (Bind t a) where
  unique (AnnBind name tag l) = do
    name' <- refreshId name
    tag' <- unique tag
    modify $ pushNewName name name'
    pure $ AnnBind name' tag' l

uniquifyBindingTVar :: TVar -> UniqableContext TVar
uniquifyBindingTVar (TV name) = do
  name' <- refreshId name
  modify $ pushNewName name name'
  pure $ TV name'

uniquifyTVar :: TVar -> UniqableContext TVar
uniquifyTVar (TV name) = TV . fromJustOrErr name <$> gets (lookupNewName name)
