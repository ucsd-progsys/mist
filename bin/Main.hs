import Language.Mist.Runner
import Language.Mist.Config
import System.Console.CmdArgs (cmdArgs)
import System.Exit
import System.IO

main :: IO ()
main = do
  config <- cmdArgs defConfig
  r <- runMist stderr config
  case r of
    Left _  -> exitFailure
    Right _ -> exitSuccess
