{-# LANGUAGE OverloadedStrings #-}

import Datatypes
import FreeCheck
import Generator
import Parser
import System.Environment (getArgs)
import Criterion.Main
import System.Directory (getDirectoryContents, doesFileExist)
import System.Exit (exitFailure)
import System.Random
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

getRandomModules :: [(Int, Module)]
getRandomModules = map genMod [13, 29, 31, 37]
  where genMod i = (i, generate (mkStdGen i) 5 5 25)

getRandomReaches :: (Signature, [(Int, Term)])
getRandomReaches = (sig, map gen [7, 11, 17, 21])
  where gen i = (i, generateP (mkStdGen i) cs 5)
        sig@(Signature cs _) = generateBlankSig 5 2

makeBenchmarks :: [(FilePath, Module)] -> [(Int, Module)] -> (Signature, [(Int, Term)]) -> [Benchmark]
makeBenchmarks namedModules rModules (sig,rReaches) = (map makeMBench namedModules) ++
                                                      (map makeRMBench rModules) ++
                                                      (map makeRRBench rReaches)
  where makeMBench (name, Module sigM trs) = bench name $ nf (checkTRS sigM) trs
        makeRMBench (i, Module sigM trs) = bench ("check random seed " ++ show i) $ nf (checkTRS sigM) trs
        makeRRBench (i, p) = bench ("getReachable random seed " ++ show i) $ nf (getReachable sig p) (TypeName "s1")

main = do
  modules <- getModules
  modules `deepseq` defaultMain (makeBenchmarks modules getRandomModules getRandomReaches)

--main = do
--  [filename] <- getArgs
--  s <- readFile filename
--  case parseModule filename s of
--    Left err -> putStrLn (show err)
--    Right (Module sig trs) -> print (checkTRS sig trs)
