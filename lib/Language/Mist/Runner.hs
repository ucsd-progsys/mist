{-# LANGUAGE ScopedTypeVariables #-}

module Language.Mist.Runner where

import qualified Control.Exception as Ex
import System.IO    
import Language.Mist.Types  
import Language.Mist.Parser
import Language.Mist.Checker 

-- import Debug.Trace (trace)

---------------------------------------------------------------------------
runMist :: Handle -> FilePath -> IO (Result Type)
---------------------------------------------------------------------------
runMist h f = act h f  
                `Ex.catch` 
                   esHandle h (return . Left) 
    
act :: Handle -> FilePath -> IO (Result Type)
act h f = do 
  s    <- readFile f  
  e    <- parse f s 
  let r = mist e 
  case r of 
    Right t -> hPutStrLn h ("Type: " ++ pprint t)
    Left _  -> return ()
  return r 

esHandle :: Handle -> ([UserError] -> IO a) -> [UserError] -> IO a
esHandle h exitF es = renderErrors es >>= hPutStrLn h >> exitF es

-----------------------------------------------------------------------------------
mist :: Bare -> Result Type 
-----------------------------------------------------------------------------------
mist = check 

--------------------------------------------------------------------------------
check :: Bare -> Result Type 
--------------------------------------------------------------------------------
check p = case wellFormed p of
            [] -> Right (typeCheck p)
            es -> Left es