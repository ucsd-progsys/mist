import Language.Mist.Types 
import Language.Mist.Runner 
import System.Environment (getArgs)
import System.Exit
import System.IO

main :: IO ()
main = do 
  f <- getSrcFile 
  r <- runMist stderr f 
  case r of 
    Left _  -> exitFailure 
    Right _ -> exitSuccess 

getSrcFile :: IO Text
getSrcFile = do
  args <- getArgs
  case args of
    [f] -> return f
    _   -> error "Please run with a single file as input"

