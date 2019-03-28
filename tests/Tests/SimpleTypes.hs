{-# LANGUAGE PatternSynonyms #-}

module Tests.SimpleTypes
  (
    T.Prim (..)
  , T.Id
  , T.Type (..), T.TVar (..), T.Ctor (..)
  , T.RType (..)

  -- -- * Abstract syntax of Mist
  , T.Expr
  , pattern Number
  , pattern AnnNumber
  , pattern Boolean
  , pattern AnnBoolean
  , pattern Unit
  , pattern AnnUnit
  , pattern Id
  , pattern AnnId
  , pattern Prim
  , pattern AnnPrim
  , pattern If
  , pattern AnnIf
  , pattern Let
  , pattern AnnLet
  , pattern App
  , pattern AnnApp
  , pattern Lam
  , pattern AnnLam
  , pattern TApp
  , pattern AnnTApp
  , pattern TAbs
  , pattern AnnTAbs

  , T.ParsedAnnotation (..)
  , T.ParsedExpr, T.ParsedBind

  , T.ElaboratedAnnotation
  , pattern T.ElabUnrefined, pattern T.ElabRefined
  , T.ElaboratedExpr, T.ElaboratedBind

  , T.Bind
  , pattern Bind
  , pattern AnnBind
  ) where

import qualified Language.Mist.Types as T
import qualified Language.Mist.UX as UX
import Text.Megaparsec.Pos (initialPos)

pattern Number i = T.Number i ()
pattern Boolean b = T.Boolean b ()
pattern Unit = T.Unit ()
pattern Id x = T.Id x ()
pattern Prim p = T.Prim p ()
pattern If e1 e2 e3 = T.If e1 e2 e3 ()
pattern Let b e1 e2 = T.Let b e1 e2 ()
pattern App e1 e2 = T.App e1 e2 ()
pattern Lam b e = T.Lam b e ()
pattern TApp e t = T.TApp e t ()
pattern TAbs alpha e = T.TAbs alpha e ()

pattern Bind x = T.Bind x ()

pattern AnnNumber i tag = T.AnnNumber i tag ()
pattern AnnBoolean b tag = T.AnnBoolean b tag ()
pattern AnnUnit tag = T.AnnUnit tag ()
pattern AnnId x tag = T.AnnId x tag ()
pattern AnnPrim p tag = T.AnnPrim p tag ()
pattern AnnIf e1 e2 e3 tag = T.AnnIf e1 e2 e3 tag ()
pattern AnnLet b e1 e2 tag = T.AnnLet b e1 e2 tag ()
pattern AnnApp e1 e2 tag = T.AnnApp e1 e2 tag ()
pattern AnnLam b e tag = T.AnnLam b e tag ()
pattern AnnTApp e t tag = T.AnnTApp e t tag ()
pattern AnnTAbs alpha e tag = T.AnnTAbs alpha e tag ()

pattern AnnBind {bindId, bindAnn} = T.AnnBind{ T.bindId = bindId
                                             , T.bindAnn = bindAnn
                                             , T.bindTag = ()}

instance UX.Located () where
  sourceSpan () = UX.SS
    { UX.ssBegin = initialPos "test"
    , UX.ssEnd = initialPos "test"
    }
