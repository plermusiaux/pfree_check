{-# LANGUAGE OverloadedStrings #-}

import Criterion.Main

import Control.Monad (filterM)
import Data.Either (partitionEithers)
import Data.Set (empty)

import System.Directory (getDirectoryContents, doesFileExist)
import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.IO (hPutStrLn, stderr)
import System.Random

import Control.DeepSeq (deepseq)

import Datatypes
import FreeCheck
import Generator
import Parser

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
getRandomModules = map genMod [11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53]
  where genMod i = (i, Module sig (genTRS s2 sig))
          where (s1, s2) = split (mkStdGen i)
                sig = genSig s1
        genTRS g sig = generateTRS sig g 100 25        -- nb_sb_rhs = 100, nb_rules = 25
        genSig g = Signature cs fs
          where (cs, sorts) = generateBlankSig s1 6 2 -- arity = 6, nb_sort = 2
                fs = generateFunc g 50 50 cs sorts    -- nb_sb_p = 50, nb_sb_q = 50
                (s1, s2) = split g

getRandomReaches :: [(Int, Signature, Term)]
getRandomReaches = map gen [11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53]
  where gen i = (i, Signature cs [], generateP s2 cs 100) -- nb_sb_p = 100
          where (s1, s2) = split (mkStdGen i)
                (cs, _) = generateBlankSig s1 6 2       -- arity = 6, nb_sort = 2

getRandomPfree :: [(Int, Module)]
getRandomPfree = map genMod [11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53]
  where genMod i = (i, Module sig (genTRS s2 sig))
          where (s1, s2) = split (mkStdGen i)
                sig = genSig s1
        genTRS g sig = generateTRS sig g 100 1        -- nb_sb_rhs = 100, nb_rules = 1
        genSig g = Signature cs fs 
          where (cs, sorts) = generateBlankSig s1 6 2 -- arity = 6, nb_sort = 2
                fs = generateFunc s2 50 50 cs sorts   -- nb_sb_p = 50, nb_sb_q = 50
                (s1, s2) = split g

makeBenchmarks :: [(FilePath, Module)] -> [(Int, Module)] -> [(Int, Signature, Term)] -> [(Int, Module)] -> [Benchmark]
makeBenchmarks namedModules rModules rReaches rPfree = [ bgroup "default" $ makeModuleBenches,
                                                         bgroup "getReachable" $ map makeRRBench rReaches,
                                                         bgroup "pFreeCheck" $ map makePFBench rPfree ]
  where makeRRBench (i, sig, p) = bench ("random seed " ++ show i) $ nf (getReachable sig (AType "s1" p)) empty
        makePFBench (i, Module sigM trs) = bench ("random seed " ++ show i) $ nf (checkTRS sigM) trs
        makeModuleBenches = (map makeMBench namedModules) ++ (map makeRMBench rModules)
          where makeMBench (name, Module sigM trs) = bench name $ nf (checkTRS sigM) trs
                makeRMBench (i, Module sigM trs) = bench ("random seed " ++ show i) $ nf (checkTRS sigM) trs

main = do
  modules <- getModules
  (modules, rModules, rReaches, rPfree) `deepseq` defaultMain (makeBenchmarks modules rModules rReaches rPfree)
  where rModules = getRandomModules
        rReaches = getRandomReaches
        rPfree = getRandomPfree
