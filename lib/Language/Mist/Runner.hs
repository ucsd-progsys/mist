{-# LANGUAGE ScopedTypeVariables #-}

module Language.Mist.Runner where

import qualified Control.Exception as Ex
import System.IO
import Language.Mist.Types
import Language.Mist.Parser
import Language.Mist.Checker

-- import Debug.Trace (trace, traceM)

---------------------------------------------------------------------------
runMist :: Handle -> FilePath -> IO (Result (Core SourceSpan))
---------------------------------------------------------------------------
runMist h f = act h f
                `Ex.catch`
                   esHandle h (return . Left)

act :: Handle -> FilePath -> IO (Result (Core SourceSpan))
act h f = do
  s    <- readFile f
  e    <- parse f s
  let r = mist e
  case r of
    Right t -> hPutStrLn h ("Elaborated: " ++ pprint t)
    Left _  -> return ()
  return r

esHandle :: Handle -> ([UserError] -> IO a) -> [UserError] -> IO a
esHandle h exitF es = renderErrors es >>= hPutStrLn h >> exitF es

-----------------------------------------------------------------------------------
mist :: Bare -> Result (Core SourceSpan)
-----------------------------------------------------------------------------------
mist = check

--------------------------------------------------------------------------------
check :: Bare -> Result (Core SourceSpan)
--------------------------------------------------------------------------------
check p =
  case wellFormed p of
    [] -> elaborate p
    errors -> Left errors
