--------------------------------------------------------------------------------
-- | This module contains the code for converting an `Expr` to a "A-Normal" form.
--------------------------------------------------------------------------------

-- TODO make this a typed normalization (preserve t that we get)

module Language.Mist.Normalizer ( anormal, liftSigmas ) where

import Language.Mist.Types
import Language.Mist.Names
import Language.Mist.Checker (primType)
import Data.Maybe (fromMaybe)
import Data.Bifunctor (first, second)

--------------------------------------------------------------------------------
-- | Insert explicit unpacking of implicit sigmas
--------------------------------------------------------------------------------
type Env a = [(Id, RType () a)]
type SigmaBinds r a = [(Id, Id, ElaboratedExpr r a)]

liftSigmas :: ElaboratedExpr r a -> ElaboratedExpr r a
liftSigmas e = fst $ runFresh (anfSigmas [] e)

anfSigmas :: (MonadFresh m) => Env a -> ElaboratedExpr r a -> m (ElaboratedExpr r a, RType () a)
anfSigmas _ e@AnnNumber{} = pure (e, liftType (extractLoc e) TInt)
anfSigmas _ e@AnnBoolean{} = pure (e, liftType (extractLoc e) TBool)
anfSigmas _ e@AnnUnit{} = pure (e, liftType (extractLoc e) TUnit)
anfSigmas env e@(AnnId x _ _) =
  pure (e, fromMaybe (error "variable not found") (lookup x env))
anfSigmas _ e@(AnnPrim p _ l) = do
  typ <- primType p
  pure (e, liftType l typ)
anfSigmas env (AnnIf e1 e2 e3 tag l) = do
  (e1', bs, _) <- immSigmas env e1
  (e2', t2) <- anfSigmas env e2
  (e3', _t3) <- anfSigmas env e3
  pure (stitchUnpacks bs (AnnIf e1' e2' e3' tag l), t2)

anfSigmas _ (AnnLet (AnnBind _x Nothing _) _e1 _e2 _tag _l) =
  error "this shouldn't happen"
anfSigmas env (AnnLet b@(AnnBind x (Just (ElabRefined t)) _) e1 e2 tag l) = do
  let env' = (x, dropPreds t):env
  (e1', _) <- anfSigmas env' e1
  (e2', t2) <- anfSigmas env' e2
  pure (AnnLet b e1' e2' tag l, t2)
anfSigmas env (AnnLet b@(AnnBind x (Just (ElabAssume t)) _) e1 e2 tag l) = do
  let env' = (x, dropPreds t):env
  (e2', t2) <- anfSigmas env' e2
  pure (AnnLet b e1 e2' tag l, t2)
anfSigmas env (AnnLet b@(AnnBind x (Just (ElabUnrefined typ)) _) e1 e2 tag l) = do
  let env' = (x, liftType l typ):env
  (e1', _) <- anfSigmas env' e1
  (e2', t2) <- anfSigmas env' e2
  pure (AnnLet b e1' e2' tag l, t2)

anfSigmas env e@AnnApp{} = do
  (e', bs, t) <- anfAppSigmas env e
  pure (stitchUnpacks bs e', t)

anfSigmas _env (AnnLam (AnnBind _x Nothing _) _e _tag _l) =
  error "this shouldn't happen"
anfSigmas env (AnnLam b@(AnnBind x (Just (ElabRefined t)) _) e tag l) = do
  (e', t') <- anfSigmas ((x, dropPreds t):env) e
  pure (AnnLam b e' tag l, RFun (AnnBind x () l) (dropPreds t) t')
anfSigmas _env (AnnLam (AnnBind _x (Just ElabAssume{}) _) _e _tag _l) =
  error "this shouldn't happen"
anfSigmas env (AnnLam b@(AnnBind x (Just (ElabUnrefined typ)) _) e tag l) = do
  (e', t') <- anfSigmas ((x, liftType l typ):env) e
  pure (AnnLam b e' tag l, RFun (AnnBind x () l) (liftType l typ) t')

anfSigmas env (AnnILam b@(Bind x _) e tag l) = do
  (e', t') <- anfSigmas env e
  pure (AnnILam b e' tag l, RIFun (AnnBind x () l) (liftType l TUnit) t')
anfSigmas env (AnnTApp e typ tag l) = do
  (e', t) <- anfSigmas env e
  let t' = case t of
            RForall tvar t' -> substReftReft (unTV tvar |-> liftType l typ) t'
            RForallP tvar t' -> substReftReft (unTV tvar |-> liftType l typ) t'
            _ -> error "should not happen"
  pure (AnnTApp e' typ tag l, t')

anfSigmas env (AnnTAbs tv e tag l) = do
  (e', t) <- anfSigmas env e
  pure (AnnTAbs tv e' tag l, RForall tv t)
anfSigmas _env (AnnUnpack _x _y _e1 _e2 _tag _l) = error "todo?"

anfAppSigmas :: (MonadFresh m) => Env a -> ElaboratedExpr r a -> m (ElaboratedExpr r a, SigmaBinds r a, RType () a)
anfAppSigmas env (AnnApp e1 e2 tag l) = do
  (e1', bs1, t) <- anfAppSigmas env e1
  (e2', bs2, _) <- immSigmas env e2
  pure (AnnApp e1' e2' tag l, bs1 <> bs2, descend t)

anfAppSigmas env e = immSigmas env e

immSigmas :: (MonadFresh m) => Env a -> ElaboratedExpr r a -> m (ElaboratedExpr r a, SigmaBinds r a, RType () a)
immSigmas env e@AnnNumber{} = immExpSigma env e
immSigmas env e@AnnBoolean{} = immExpSigma env e
immSigmas env e@AnnUnit{} = immExpSigma env e
immSigmas env e@AnnId{} = immExpSigma env e
immSigmas env e@AnnPrim{} = immExpSigma env e
immSigmas env e@AnnIf{} = immExpSigma env e
immSigmas env (AnnApp e1 e2 tag l) = do
  (e1', bs1, t1) <- immSigmas env e1
  (e2', bs2, _) <- immSigmas env e2
  let t1' = descend t1
  (eapp, bsapp, tout) <- unpackAllSigmas t1' (AnnApp e1' e2' tag l)
  pure (eapp, bs1 <> bs2 <> bsapp, tout) -- TODO: is this the correct order?
immSigmas env e@AnnLet{} = immExpSigma env e
immSigmas env e@AnnLam{} = immExpSigma env e
immSigmas env e@AnnILam{} = immExpSigma env e
immSigmas env e@AnnTApp{} = immExpSigma env e
immSigmas env e@AnnTAbs{} = immExpSigma env e
immSigmas env e@AnnUnpack{} = immExpSigma env e

immExpSigma :: (MonadFresh m) => Env a -> ElaboratedExpr r a -> m (ElaboratedExpr r a, SigmaBinds r a, RType () a)
immExpSigma env e = do
  (e', t) <- anfSigmas env e
  unpackAllSigmas t e'

unpackAllSigmas :: (MonadFresh m) => RType () a -> ElaboratedExpr r a -> m (ElaboratedExpr r a, SigmaBinds r a, RType () a)
unpackAllSigmas (RIExists b _ t') e = do
  let l = extractLoc e
  let tag = extractAnn e
  (x, y) <- freshSigmaNames (bindId b)
  (e', bs, tout) <- unpackAllSigmas t' (AnnId y tag l)
  pure (e', (x, y, e):bs, tout)
unpackAllSigmas t e = do
  pure (e, [], t)

stitchUnpacks :: SigmaBinds r a -> ElaboratedExpr r a -> ElaboratedExpr r a
stitchUnpacks [] e' = e'
stitchUnpacks ((x, y, e):bs) e' =
  AnnUnpack (AnnBind x () l) (AnnBind y () l) e (stitchUnpacks bs e') (extractAnn e') (extractLoc e')
  where
    l = extractLoc e

descend :: RType r a -> RType r a
descend (RIFun _ _ t') = descend t'
descend (RFun _ _ t') = t'
descend _ = error "shouldn't happen"

dropPreds :: RType r a -> RType () a
dropPreds = first (const ())

freshSigmaNames :: (MonadFresh m) => Id -> m (Id, Id)
freshSigmaNames x = do
  x' <- refreshId x
  y <- refreshId $ "unpackedY" ++ cSEPARATOR
  pure (x', y)

liftType :: a -> Type -> RType () a
liftType loc (TVar alpha) = RBase (Bind "x" loc) (TVar alpha) ()
liftType loc TUnit = RBase (Bind "x" loc) TUnit ()
liftType loc TInt = RBase (Bind "x" loc) TInt ()
liftType loc TBool = RBase (Bind "x" loc) TBool ()
liftType loc (t1 :=> t2) = RFun (Bind "x" loc) (liftType loc t1) (liftType loc t2)
liftType loc (TCtor ctor types) = RApp ctor (fmap (second (liftType loc)) types)
liftType loc (TForall tvar typ) = RForall tvar (liftType loc typ)


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
anf (AnnILam x e tag l) = AnnILam x <$> anf e <*> pure tag <*> pure l
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
imm e@AnnILam{} = immExp e
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
