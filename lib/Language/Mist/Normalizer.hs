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
  -- pure $ Let (first Just x) e' b' l
  pure $ AnnLet x e' b' tag l
-- anf (Prim2 o e1 e2 l) = do
--   (bs, e1') <- imm e1
--   (bs', e2') <- imm e2
--   let bs'' = bs' ++ bs
--   pure $ stitch bs'' (Prim2 o e1' e2' l)
anf (AnnIf c e1 e2 tag l) = do
  (bs, c') <- imm c
  e1' <- anf e1
  e2' <- anf e2
  pure $ stitch bs (AnnIf c' e1' e2' tag l)

-- anf i (Tuple e1 e2 l)   = (i', stitch bs (Tuple e1' e2' l))
--   where
--     (i', bs, [e1',e2']) = imms i [e1, e2]

-- anf i (GetItem e1 f l)  = (i', stitch bs (GetItem e1' f l))
--   where
--     (i', bs, e1')       = imm i e1

anf (AnnApp e1 e2 tag l) = do
  (bs, e1') <- imm e1
  (bs', e2') <- imm e2
  pure $ stitch (bs ++ bs') (AnnApp e1' e2' tag l)
-- anf (Lam x e l) = Lam (first Just x) <$> anf e <*> pure l
anf (AnnLam x e tag l) = AnnLam x <$> anf e <*> pure tag <*> pure l
anf (AnnTApp e t tag l) = AnnTApp <$> anf e <*> pure t <*> pure tag <*> pure l
anf (AnnTAbs alpha e tag l) = AnnTAbs alpha <$> anf e <*> pure tag <*> pure l


--------------------------------------------------------------------------------
-- | `stitch bs e` takes a "context" `bs` which is a list of temp-vars and their
--   definitions, and an expression `e` that uses the temp-vars in `bs` and glues
--   them together into a `Let` expression.
--------------------------------------------------------------------------------
stitch :: Binds t a -> AnfExpr t a -> AnfExpr t a
--------------------------------------------------------------------------------
stitch bs e = bindsExpr [(x, e) | (x, (e, _)) <- reverse bs] e (extractAnn e) (extractLoc e)

--------------------------------------------------------------------------------
-- | `imm i e` takes as input a "start" counter `i` and expression `e` and
--   returns an output `(i', bs, e')` where
--   * `i'` is the output counter (i.e. i' - i) anf-variables were generated,
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
-- imm (Prim2 o e1 e2 l) = do
--   (bs, v1) <- imm e1
--   (bs', v2) <- imm e2
--   x <- freshBind l
--   let bs'' = (x, (Prim2 o v1 v2 l, l)) : (bs ++ bs')
--   pure (bs'', mkId x l)

-- imm i (Tuple e1 e2 l)   = (i'', bs', mkId x l)
--   where
--     (i', bs, [v1, v2])  = imms  i [e1, e2]
--     (i'', x)            = fresh l i'
--     bs'                 = (x, (Tuple v1 v2 l, l)) : bs

-- imm i (GetItem e1 f l)  = (i'', bs', mkId x l)
--   where
--     (i', bs, v1)        = imm i e1
--     (i'', x)            = fresh l i'
--     bs'                 = (x, (GetItem v1 f l, l)) : bs

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


{-
anf1 := "add1(add1(add1(add1(x))))"

let t1 = add1(x)
  , t2 = add1(t1)
  , t3 = add1(t2)
  , t4 = add1(t3)
in
    t4

anf2 := ((2 + 3) * (12 - 4)) * (7 + 8)

 let t1 = 2  + 3
   , t2 = 12 - 4
   , t3 = t1 * t2
   , t4 = 7 + 8
 in
     t3 * t4

anf3 := (let x = 10 in x + 5) + (let y = 20 in y - 5)

let  t1 = let x = 10 in
           x + 5
   , t2 = let y = 20 in
           y - 5
in
   t1 + t2

anf4 := (if x: y + 1 else: z + 1) + 12
let t = (if ...)
in t + 12

-}
