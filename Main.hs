import Datatypes
import FreeCheck
import Parser
import System.Environment (getArgs)

main = do
  [filename] <- getArgs
  s <- readFile filename
  case parseModule filename s of
    Left err -> putStrLn (show err)
    Right (Module sig trs) -> print (checkTRS sig trs)
