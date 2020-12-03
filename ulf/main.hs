{-# Language BlockArguments #-}
{-# language ScopedTypeVariables #-}

import Control.Monad
import Options.Applicative
import Source.Parser (src)
import Control.Exception
import Text.Megaparsec (parse, errorBundlePretty)
import System.Exit
import Elaborate.Check (infer)
import Elaborate.Value
import Common.Qty
import Elaborate.Term
import Elaborate.Zonk
import Solver.Sat.CaDiCaL

type Command = ParserInfo (IO ())

checkFile :: FilePath -> Bool -> IO Bool
checkFile p _ = readFile p >>= \txt ->
  case parse src p txt of
    Left e -> do
      putStrLn $ errorBundlePretty e
      pure False
    Right r -> runSolver $ do
      (qs, tm, ty) <- infer emptyCtx r
      tm' <- zonk VNil tm
      s <- showTmIO [] tm'
      print_statistics
      putStrLn s
      pure True

runCheck :: [FilePath] -> Bool -> IO ()
runCheck fs el = do
  bs <- forM fs (\x -> checkFile x el `catch` (\(e :: SomeException) -> do
    putStrLn $ "Error while checking " ++ x ++ ":"
    putStrLn $ displayException e
    pure False))
  when (not $ and bs) $ exitFailure

runServer :: IO ()
runServer = putStrLn "serving"

checkCommand :: Command
checkCommand = info (helper <*> (runCheck <$> some file <*> elaborate))
   $ fullDesc
  <> progDesc "Type check a program"
  <> header "ergo check"
  where 
     file = strArgument
        $ metavar "FILES..." 
       <> action "file"
       <> help (unlines 
          [ "Input source files" 
          ])
     elaborate = switch 
        $ long "elaborate" 
       <> help "Print elaborated syntax after type checking"

serverCommand :: Command
serverCommand = info (pure runServer)
   $ fullDesc
  <> progDesc "Start the language server"
  <> header "ergo server"

commands :: Parser (IO ())
commands = subparser 
   $ command "check" checkCommand
  <> command "server" serverCommand

optionsParser :: Command
optionsParser = info (helper <*> commands)
   $ fullDesc
  <> progDesc "ergo compiler"
  <> header "ergo"
  
main :: IO ()
main = join $ execParser optionsParser
  
