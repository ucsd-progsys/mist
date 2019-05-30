--------------------------------------------------------------------------------
-- | This module contains the code for converting an `Expr` to a "A-Normal" form.
--------------------------------------------------------------------------------

-- TODO make this a typed normalization (preserve t that we get)

module Language.Mist.Normalizer ( anormal ) where

import Language.Mist.Types
import Language.Mist.Names


type Binds t a = [(Bind t a, (AnfExpr t a, a))] -- TODO: is there a reason for this not to be a triple?

--------------------------------------------------------------------------------
-- | Convert an Expr into A-Normal Form
--------------------------------------------------------------------------------
anormal :: Expr t a -> AnfExpr t a
--------------------------------------------------------------------------------
anormal e = runFresh (anf e)

--------------------------------------------------------------------------------
anf :: (MonadFresh m) => Expr t a -> m (AnfExpr t a)
--------------------------------------------------------------------------------
anf e@AnnUnit{} = pure e
anf e@AnnNumber{} = pure e
anf e@AnnBoolean{} = pure e
anf e@AnnId{} = pure e
anf e@AnnPrim{} = pure e
anf (AnnLet x e b tag l) = do
  e' <- anf e
  b' <- anf b
  pure $ AnnLet x e' b' tag l
anf (AnnIf c e1 e2 tag l) = do
  (bs, c') <- imm c
  e1' <- anf e1
  e2' <- anf e2
  pure $ stitch bs (AnnIf c' e1' e2' tag l)
anf e@AnnApp{} = uncurry stitch <$> anfApp e
anf (AnnLam x e tag l) = AnnLam x <$> anf e <*> pure tag <*> pure l
anf e@AnnTApp{}  = uncurry stitch <$> anfApp e
anf (AnnTAbs alpha e tag l) = AnnTAbs alpha <$> anf e <*> pure tag <*> pure l

anfApp (AnnApp e1 e2 tag l) = do
  (bs, e1') <- anfApp e1
  (bs', e2') <- imm e2
  pure (bs ++ bs', AnnApp e1' e2' tag l)
anfApp (AnnTApp e1 t tag l) = do
  (bs, e1') <- anfApp e1
  pure (bs, AnnTApp e1' t tag l)
anfApp e = imm e

--------------------------------------------------------------------------------
-- | `stitch bs e` takes a "context" `bs` which is a list of temp-vars and their
--   definitions, and an expression `e` that uses the temp-vars in `bs` and glues
--   them together into a `Let` expression.
--------------------------------------------------------------------------------
stitch :: Binds t a -> AnfExpr t a -> AnfExpr t a
--------------------------------------------------------------------------------
stitch bs e = bindsExpr [(x, e) | (x, (e, _)) <- reverse bs] e (extractAnn e) (extractLoc e)

--------------------------------------------------------------------------------
-- | `imm e` takes as input an expression `e` and
--   returns an output `(bs, e')` where
--   * `bs` are the temporary binders needed to render `e` in ANF, and
--   * `e'` is an `imm` value Id equivalent to `e`.
--------------------------------------------------------------------------------
imm :: (MonadFresh m) => Expr t a -> m (Binds t a, ImmExpr t a)
--------------------------------------------------------------------------------
imm e@AnnUnit{} = immExp e
imm e@AnnNumber{} = immExp e
imm e@AnnBoolean{} = immExp e
imm e@AnnPrim{} = immExp e
imm e@AnnId{} = pure ([], e)
imm (AnnApp e1 e2 tag l) = do
  (bs, v1) <- imm e1
  (bs', v2) <- imm e2
  x <- freshBind tag l
  let bs'' = (x, (AnnApp v1 v2 tag l, l)) : (bs ++ bs')
  pure (bs'', mkId x tag l)
imm e@AnnIf{} = immExp e
imm e@AnnLet{} = immExp e
imm e@AnnLam{} = immExp e
imm e@AnnTApp{} = immExp e
imm e@AnnTAbs{} = immExp e

immExp :: (MonadFresh m) => Expr t a -> m (Binds t a, ImmExpr t a)
immExp e = do
  let l = extractLoc e
  let t = extractAnn e
  e' <- anf e
  v <- freshBind t l
  let bs = [(v, (e', l))]
  pure (bs, mkId v t l)

freshBind :: (MonadFresh m) => t -> a -> m (Bind t a)
freshBind t l = do
  x <- refreshId $ "anf" ++ cSEPARATOR
  pure AnnBind { bindId = x
               , bindAnn = t
               , bindTag = l
               }

mkId :: Bind t a -> t -> a -> Expr t a
mkId x tag l = AnnId (bindId x) tag l

bindsExpr :: [(Bind t a, Expr t a)] -> Expr t a -> t -> a -> Expr t a
bindsExpr bs e t l = foldr (\(x, e1) e2 -> AnnLet x e1 e2 t l) e bs
