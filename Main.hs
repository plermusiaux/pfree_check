import Data.List ( nub )
import System.Console.GetOpt
import System.Environment ( getArgs )
import System.Exit
import System.IO ( hPutStrLn, stderr )

import Datatypes
import FreeCheck
import FreeCheckNL ( checkTRSnl )
import Parser

data Flag = NonLinear             -- -p --non-linear
          | Help                  -- -h --help
          deriving (Eq,Ord,Enum,Show,Bounded)

flags = [ Option ['p']    ["non-linear"] (NoArg NonLinear)
            "Run a full non-linear analysis"
         ,Option ['h'] ["help"]       (NoArg Help)
            "Print this help message"
        ]

parse argv = case getOpt Permute flags argv of

  (args,[filename],[]) -> do
      if Help `elem` args
          then do hPutStrLn stderr (usageInfo header flags)
                  exitWith ExitSuccess
          else return (nub args, filename)

  (_,_,errs)   -> do
      hPutStrLn stderr (concat errs ++ usageInfo header flags)
      exitWith (ExitFailure 1)

  where header = "Usage: ./Main file [--non-linear]"

main = do
  (flags, filename) <- getArgs >>= parse
  s <- readFile filename
  case parseModule filename s of
    Left err               -> putStrLn (show err)
    Right (Module sig trs) -> if elem NonLinear flags
                              then print (checkTRSnl sig trs)
                              else print (checkTRS sig trs)

