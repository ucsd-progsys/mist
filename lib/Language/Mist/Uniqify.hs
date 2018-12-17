{-# LANGUAGE TypeSynonymInstances  #-}
{-# LANGUAGE FlexibleInstances  #-}
module Language.Mist.Uniqify (uniqify, varNum) where

import Control.Monad.State
import Data.Map.Strict as M
import Data.List.Split
import Language.Mist.Types

cSEPERATOR = "##"

refreshSep x n = x ++ cSEPERATOR ++ show n
varNum :: String -> Int
varNum = read . last . splitOn cSEPERATOR

type Fresh = State (Int, Map String String)

uniqify :: Expr a -> Expr a
uniqify e = evalState (refresh e) (0, M.empty)

class Refresh a where
    refresh :: a -> Fresh a

instance Refresh (Expr a) where
  refresh e@Number{} = pure e
  refresh e@Boolean{} = pure e
  refresh e@Unit{} = pure e
  refresh  (Id s l) = do
      m <- gets snd
      let Just new = M.lookup s m
      pure $ Id new l
  refresh  (Prim2 o e1 e2 l) =
      Prim2 o <$> refresh e1 <*> refresh e2 <*> pure l
  refresh  (If e1 e2 e3 l) =
      If <$> refresh e1 <*> refresh e2 <*> refresh e3 <*> pure l
  refresh  (App e1 e2 l) =
      App <$> refresh e1 <*> refresh e2 <*> pure l
  refresh  (Tuple e1 e2 l) =
      Tuple <$> refresh e1 <*> refresh e2 <*> pure l
  refresh  (GetItem e1 f l) =
      GetItem <$> refresh e1 <*> pure f <*> pure l
  refresh  (Let b sig ex e l) =
      Let <$> refresh b <*> refresh sig <*> refresh ex <*> refresh e <*> pure l
  refresh  (Lam bs e l) = Lam <$> refresh bs <*> refresh e <*> pure l

instance Refresh String where
  refresh x = do
      (n, m) <- get
      let x' = refreshSep x n
      put (n+1, M.insert x x' m)
      pure x'

instance Refresh (Bind a) where
  refresh (Bind x lx) = Bind <$> refresh x <*> pure lx

instance Refresh [Bind a] where
  refresh = mapM refresh

instance Refresh (Sig a) where
  refresh Infer = pure Infer
  refresh (Check s) = Check <$> refresh s
  refresh (Assume s) = Assume <$> refresh s

instance Refresh (e a) =>  Refresh (RPoly e a) where
  refresh (RForall tvs rt) = RForall <$> refresh tvs <*> refresh rt

instance Refresh [TVar] where
  refresh = mapM refresh

instance Refresh TVar where
  refresh (TV a) =  TV <$> refresh a

instance Refresh (e a) => Refresh (RType e a) where
  refresh (RBase b t e) =
    RBase <$> refresh b <*> refresh t <*> refresh e
  refresh (RFun b rt1 rt2) =
    RFun <$> refresh b <*> refresh rt1 <*> refresh rt2
  refresh (RRTy b rt e) =
    RRTy <$> refresh b <*> refresh rt <*> refresh e

instance Refresh Type where
  refresh (TVar t) = TVar <$> refresh t
  refresh TInt = pure TInt
  refresh TBool = pure TBool
  refresh (t1 :=> t2) = (:=>) <$> mapM refresh t1 <*> refresh t2
  refresh (TPair t1 t2) = TPair <$> refresh t1 <*> refresh t2
  refresh (TCtor c ts) = TCtor c <$> mapM refresh ts
