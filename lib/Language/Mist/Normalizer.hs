--------------------------------------------------------------------------------
-- | This module contains the code for converting an `Expr` to a "A-Normal" form.
--------------------------------------------------------------------------------

module Language.Mist.Normalizer ( anormal ) where

import Language.Mist.Types
import Language.Mist.Names

import Data.Bifunctor

type Binds t a = [(Bind a, (AnfExpr t a, a))] -- TODO: is there a reason for this not to be a triple?

--------------------------------------------------------------------------------
-- | Convert an Expr into A-Normal Form
--------------------------------------------------------------------------------
anormal :: Expr t a -> AnfExpr t a
--------------------------------------------------------------------------------
anormal e = runFresh (anf e)

--------------------------------------------------------------------------------
-- | `anf i e` takes as input a "start" counter `i` and expression `e` and
--   returns an output `(i', e')` where
--   * `i'` is the output counter (i.e. i' - i) anf-variables were generated,
--   * `e'` is equivalent to `e` but is in A-Normal Form.
--------------------------------------------------------------------------------
anf :: (MonadFresh m) => Expr t a -> m (AnfExpr t a)
--------------------------------------------------------------------------------
anf (Unit l) = pure $ Unit l
anf (Number n l) = pure $ Number n l
anf (Boolean b l) = pure $ Boolean b l
anf (Id x l) = pure $ Id x l
anf (Let x e b l) = do
  e' <- anf e
  b' <- anf b
  pure $ Let (first Just x) e' b' l
anf (Prim2 o e1 e2 l) = do
  (bs, e1') <- imm e1
  (bs', e2') <- imm e2
  let bs'' = bs' ++ bs
  pure $ stitch bs'' (Prim2 o e1' e2' l)
anf (If c e1 e2 l) = do
  (bs, c') <- imm c
  e1' <- anf e1
  e2' <- anf e2
  pure $ stitch bs (If c' e1' e2' l)

-- anf i (Tuple e1 e2 l)   = (i', stitch bs (Tuple e1' e2' l))
--   where
--     (i', bs, [e1',e2']) = imms i [e1, e2]

-- anf i (GetItem e1 f l)  = (i', stitch bs (GetItem e1' f l))
--   where
--     (i', bs, e1')       = imm i e1

anf (App e1 e2 l) = do
  (bs, e1') <- imm e1
  (bs', e2') <- imm e2
  pure $ stitch (bs ++ bs') (App e1' e2' l)
anf (Lam x e l) = Lam (first Just x) <$> anf e <*> pure l
anf (TApp e t l) = TApp <$> anf e <*> pure t <*> pure l
anf (TAbs alpha e l) = TAbs alpha <$> anf e <*> pure l


--------------------------------------------------------------------------------
-- | `stitch bs e` takes a "context" `bs` which is a list of temp-vars and their
--   definitions, and an expression `e` that uses the temp-vars in `bs` and glues
--   them together into a `Let` expression.
--------------------------------------------------------------------------------
stitch :: Binds t a -> AnfExpr t a -> AnfExpr t a
--------------------------------------------------------------------------------
stitch bs e = bindsExpr [(x, e) | (x, (e, _)) <- reverse bs] e (extract e)

--------------------------------------------------------------------------------
-- | `imm i e` takes as input a "start" counter `i` and expression `e` and
--   returns an output `(i', bs, e')` where
--   * `i'` is the output counter (i.e. i' - i) anf-variables were generated,
--   * `bs` are the temporary binders needed to render `e` in ANF, and
--   * `e'` is an `imm` value Id equivalent to `e`.
--------------------------------------------------------------------------------
imm :: (MonadFresh m) => Expr t a -> m (Binds t a, ImmExpr t a)
--------------------------------------------------------------------------------
imm e@Unit{} = immExp e
imm e@Number{} = immExp e
imm e@Boolean{} = immExp e
imm (Id x l) = pure ([], Id x l)
imm (Prim2 o e1 e2 l) = do
  (bs, v1) <- imm e1
  (bs', v2) <- imm e2
  x <- freshBind l
  let bs'' = (x, (Prim2 o v1 v2 l, l)) : (bs ++ bs')
  pure (bs'', mkId x l)

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

imm (App e1 e2 l) = do
  (bs, v1) <- imm e1
  (bs', v2) <- imm e2
  x <- freshBind l
  let bs'' = (x, (App v1 v2 l, l)) : (bs ++ bs')
  pure (bs'', mkId x l)
imm e@If{} = immExp e
imm e@Let{} = immExp e
imm e@Lam{} = immExp e
imm e@TApp{} = immExp e
imm e@TAbs{} = immExp e

immExp :: (MonadFresh m) => Expr t a -> m (Binds t a, ImmExpr t a)
immExp e = do
  let l = extract e
  e' <- anf e
  v <- freshBind l
  let bs = [(v, (e', l))]
  pure (bs, mkId v l)

freshBind :: (MonadFresh m) => a -> m (Bind a)
freshBind l = do
  x <- refreshId $ "anf" ++ cSEPARATOR
  pure Bind { _bindId = x
            , _bindLabel = l
            }

mkId :: (Binder b) => b a -> a -> Expr t a
mkId x l = Id (bindId x) l


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
