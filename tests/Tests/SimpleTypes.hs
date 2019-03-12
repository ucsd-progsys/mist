{-# LANGUAGE PatternSynonyms #-}

module Tests.SimpleTypes
  (
    T.Prim2 (..)
  , T.Id
  , T.Type (..), T.TVar (..), T.Ctor (..)
  , T.RType (..)

  -- -- * Abstract syntax of Mist
  , T.Expr
  , pattern Number
  , pattern Boolean
  , pattern Unit
  , pattern Id
  , pattern Prim2
  , pattern If
  , pattern Let
  , pattern App
  , pattern Lam
  , pattern TApp
  , pattern TAbs

  , T.ParsedType (..)
  , T.ParsedExpr, T.ParsedAnnBind, T.ParsedDef

  , T.ElaboratedType
  , pattern T.ElabUnrefined, pattern T.ElabRefined
  , T.ElaboratedExpr, T.ElaboratedAnnBind

  , T.Bind
  , pattern Bind

  , T.AnnBind
  , pattern AnnBind

  , T.Field (..)
  ) where

import qualified Language.Mist.Types as T
import qualified Language.Mist.UX as UX
import Text.Megaparsec.Pos (initialPos)

pattern Number i = T.Number i ()
pattern Boolean b = T.Boolean b ()
pattern Unit = T.Unit ()
pattern Id x = T.Id x ()
pattern Prim2 p e1 e2 = T.Prim2 p e1 e2 ()
pattern If e1 e2 e3 = T.If e1 e2 e3 ()
pattern Let b e1 e2 = T.Let b e1 e2 ()
-- pattern Tuple e1 e2 = T.GetItem e1 e2 ()
-- pattern GetItem e1 f = T.GetItem e1 f ()
pattern App e1 e2 = T.App e1 e2 ()
pattern Lam b e = T.Lam b e ()
pattern TApp e t = T.TApp e t ()
pattern TAbs alpha e = T.TAbs alpha e ()

pattern Bind x = T.Bind { T._bindId = x
                        , T._bindLabel = ()
                        }


pattern AnnBind x t = T.AnnBind { T._aBindId = x
                                , T._aBindType = t
                                , T._aBindLabel = ()}

instance UX.Located () where
  sourceSpan () = UX.SS
    { UX.ssBegin = initialPos "test"
    , UX.ssEnd = initialPos "test"
    }
