{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}

module Language.Mist.Config (
    Config (..)
  , defConfig
) where

import GHC.Generics
import System.Console.CmdArgs

data Config = Config
  { srcFile     :: FilePath            -- ^ src file (*.hs, *.ts, *.c, or even *.fq or *.bfq)
  , readInput   :: Bool
  } deriving (Eq, Data, Typeable, Show, Generic)

instance Default Config where
  def = defConfig

defConfig :: Config
defConfig = Config
  { srcFile   = "out"   &= args &= typFile
  , readInput = False   &= name "read" &= help "Use the reader instead of the parser"
  }
  &= verbosity
  &= program "mist"
  -- &= help    "Predicate Abstraction Based Horn-Clause Solver"
  -- &= summary "fixpoint Copyright 2009-15 Regents of the University of California."
  -- &= details [ "Predicate Abstraction Based Horn-Clause Solver"
  --            , ""
  --            , "To check a file foo.fq type:"
  --            , "  fixpoint foo.fq"
  --            ]
