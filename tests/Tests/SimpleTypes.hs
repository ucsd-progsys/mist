{-# LANGUAGE PatternSynonyms #-}

module Tests.SimpleTypes
  (
    T.Prim2 (..)
  , T.Id
  , T.Sig (..), T.Type (..), T.TVar (..), T.Ctor (..)
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
  , pattern GetItem
  , pattern App
  , pattern Lam

  , T.Bind
  , pattern Bind


  , T.Core
  , pattern CNumber
  , pattern CBoolean
  , pattern CUnit
  , pattern CId
  , pattern CPrim2
  , pattern CIf
  , pattern CLet
  , pattern CTuple
  , pattern CPrim
  , pattern CApp
  , pattern CLam
  , pattern CTApp
  , pattern CTAbs

  , T.AnnBind
  , pattern AnnBind

  , T.Prim (..)

  , T.Field (..)
  ) where

import qualified Language.Mist.Types as T

pattern Number i = T.Number i ()
pattern Boolean b = T.Boolean b ()
pattern Unit = T.Unit ()
pattern Id x = T.Id x ()
pattern Prim2 p e1 e2 = T.Prim2 p e1 e2 ()
pattern If e1 e2 e3 = T.If e1 e2 e3 ()
pattern Let b s e1 e2 = T.Let b s e1 e2 ()
pattern GetItem e1 f = T.GetItem e1 f ()
pattern App e1 e2 = T.App e1 e2 ()
pattern Lam b e = T.Lam b e ()

pattern Bind x = T.Bind { T.bindId = x
                        , T.bindLabel = ()
                        }


pattern CNumber i = T.CNumber i ()
pattern CBoolean b = T.CBoolean b ()
pattern CUnit = T.CUnit ()
pattern CId x = T.CId x ()
pattern CPrim2 p e1 e2 = T.CPrim2 p e1 e2 ()
pattern CIf e1 e2 e3 = T.CIf e1 e2 e3 ()
pattern CLet b e1 e2 = T.CLet b e1 e2 ()
pattern CTuple e1 e2 = T.CTuple e1 e2 ()
pattern CPrim p = T.CPrim p ()
pattern CApp e1 e2 = T.CApp e1 e2 ()
pattern CLam b e = T.CLam b e ()
pattern CTApp e t = T.CTApp e t ()
pattern CTAbs t e = T.CTAbs t e ()


pattern AnnBind x t = T.AnnBind { T.aBindId = x
                                , T.aBindType = t
                                , T.aBindLabel = ()}
