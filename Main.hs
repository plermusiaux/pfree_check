{-# LANGUAGE OverloadedStrings #-}

import Datatypes
import FreeCheck
import Parser
import System.Environment (getArgs)
import Criterion.Main
import System.Directory (getDirectoryContents, doesFileExist)
import System.Exit (exitFailure)
import Data.Either (partitionEithers)
import System.IO (hPutStrLn, stderr)
import Control.DeepSeq (deepseq)
import Control.Monad (filterM)

collect :: [Either a b] -> Either [a] [b]
collect es = select (partitionEithers es)
  where select (xs, ys) | null xs = Right ys
                        | otherwise = Left xs

getModules :: IO [(FilePath, Module)]
getModules = do
  examples <- getDirectoryContents "."
  files <- filterM doesFileExist examples
  filesContent <- mapM readFile files
  case collect (zipWith parseModule files filesContent) of
    Left errors -> do
      mapM_ (hPutStrLn stderr . show) errors
      exitFailure
    Right modules ->
      return (zip files modules)

makeBenchmarks :: [(FilePath, Module)] -> [Benchmark]
makeBenchmarks namedModules = map makeBench namedModules
  where makeBench (name, Module sig trs) = bench name $ nf (checkTRS sig) trs

main = do
  modules <- getModules
  modules `deepseq` defaultMain (makeBenchmarks modules)

--main = do
--  [filename] <- getArgs
--  s <- readFile filename
--  case parseModule filename s of
--    Left err -> putStrLn (show err)
--    Right (Module sig trs) -> print (checkTRS sig trs)
