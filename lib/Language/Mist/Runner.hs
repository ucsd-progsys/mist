{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}

module Language.Mist.Runner where

import qualified Control.Exception as Ex
import System.IO
import Language.Mist.Types
import Language.Mist.Parser
import Language.Mist.Checker
import Language.Mist.CGen
import Language.Mist.ToFixpoint
import Language.Mist.Normalizer
import Language.Mist.Names
import qualified Language.Fixpoint.Horn.Types as HC
import qualified Language.Fixpoint.Types as F

import Text.Megaparsec.Pos (initialPos) -- NOTE: just for debugging

type R = HC.Pred

deriving instance Show HC.Pred -- NOTE: just for debugging

---------------------------------------------------------------------------
runMist :: Handle -> FilePath -> IO (Result (ElaboratedExpr R SourceSpan))
---------------------------------------------------------------------------
runMist h f = act h f
                `Ex.catch`
                   esHandle h (return . Left)

act :: Handle -> FilePath -> IO (Result (ElaboratedExpr R SourceSpan))
act _h f = do
  s    <- readFile f
  e    <- parse f s
  let r = mist e
  case r of
    Right t -> do
      -- hPutStrLn h ("Elaborated: " ++ show t) >>
      --(print c >> solve c >>= print)
      let c = generateConstraints (anormal t) -- TODO: move this into the mist function
      solverResult <- print c >> solve c
      case F.resStatus solverResult of
        F.Safe -> return r
        _ -> return $ Left [mkError "solver failed" (SS {ssBegin = initialPos "file", ssEnd = initialPos "file"})] -- TODO: proper error
    Left _ -> return r

esHandle :: Handle -> ([UserError] -> IO a) -> [UserError] -> IO a
esHandle h exitF es = renderErrors es >>= hPutStrLn h >> exitF es

-----------------------------------------------------------------------------------
mist :: BareExpr -> Result (ElaboratedExpr R SourceSpan)
-----------------------------------------------------------------------------------
mist expr = do
  case wellFormed expr of
    [] -> do
      let uniqueExpr = uniquify expr
      let predExpr = parsedExprPredToFixpoint uniqueExpr
      elaborate predExpr
    errors -> Left errors
