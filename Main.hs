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
getRandomModules = map genMod [13, 29, 37, 43]
  where genMod i = (i, Module sig (genTRS s2 sig))
          where (s1, s2) = split (mkStdGen i)
                sig = genSig s1
        (cs, sorts) = generateBlankSig 5 2                    -- arity = 5, nb_sort = 2
        genSig g = Signature cs (generateFunc g 6 4 cs sorts) -- depth = 6, depth_annotation = 4
        genTRS g sig = generateTRS sig g 3 25                 -- depth_rhs = 3, nb_rules = 25

getRandomReaches :: (Signature, [(Int, Term)])
getRandomReaches = (Signature cs [], map gen [7, 11, 17, 23])
  where gen i = (i, generateP (mkStdGen i) cs 8) -- depth = 8
        (cs, _) = generateBlankSig 5 2 -- arity = 5, nb_sort = 2

makeBenchmarks :: [(FilePath, Module)] -> [(Int, Module)] -> (Signature, [(Int, Term)]) -> [Benchmark]
makeBenchmarks namedModules rModules (sig,rReaches) = (map makeMBench namedModules) ++
                                                      (map makeRMBench rModules) ++
                                                      (map makeRRBench rReaches)
  where makeMBench (name, Module sigM trs) = bench name $ nf (checkTRS sigM) trs
        makeRMBench (i, Module sigM trs) = bench ("check random seed " ++ show i) $ nf (checkTRS sigM) trs
        makeRRBench (i, p) = bench ("getReachable random seed " ++ show i) $ nf (snd.(getReachable emptyCache sig p)) (TypeName "s1")

main = do
  modules <- getModules
  (modules, rModules, rReaches) `deepseq` defaultMain (makeBenchmarks modules rModules rReaches)
  where rModules = getRandomModules
        rReaches = getRandomReaches

