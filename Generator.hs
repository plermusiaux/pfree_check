module Generator (
  generateBlankSig,
  generateFunc,
  generateP,
  generateTRS) where

import Datatypes
import Signature

import qualified Data.Map as M
import Data.Maybe
import System.Random

generateBlankSig :: RandomGen g => g -> Int -> Int -> ([Constructor], [TypeName])
generateBlankSig seed ar nb = (constructors, sorts)
  where sorts = [ TypeName ("s" ++ (show i)) | i <- [1..nb] ]
        rBsl = zip3 (genSeedList s1 nb) (rBoolList s2 nb) sorts
        constructors = concatMap (generateConst ar sorts) rBsl
        (s1, s2) = split seed

generateP :: RandomGen g => g -> [Constructor] -> Int -> Term
generateP _ _ 0 = AVar (VarName "_") Unknown
generateP seed cs nb = Appl rC (map genSub rDistl)
  where (s1, s2) = split seed
        Constructor rC _ _ = getRandom seed cs
        dom = domain (Signature cs []) rC
        ar = length dom
        rDistl = zip3 (genSeedList s1 ar) (rDistList s2 ar (nb-1)) dom
        genSub (seedi, nbi, si) = generatePattern seedi cs nbi si

generateConst :: RandomGen g => Int -> [TypeName] -> (g, Bool, TypeName)  -> [Constructor]
generateConst ar sorts (seed, b, range@(TypeName s))
  | b          = c : map createConst [1..nb^ar]
  | rBool seed = c : map createConst [1..nb^ar]
  | otherwise  = map createConst [1..nb^ar]
  where nb = length sorts
        c = Constructor (FunName ("c" ++ s)) [] range
        createConst i = Constructor name domain range
          where name = FunName ("c" ++ (show i) ++ "_" ++ s)
                domain = generateDomain ar (i-1) sorts

generateDomain :: Int -> Int -> [TypeName] -> [TypeName]
generateDomain ar i sorts = map (sorts!!) (map f [1..ar])
  where f k = (i `mod` (nb^k)) `div` (nb^(k-1))
        nb = length sorts

generateFunc :: RandomGen g => g -> Int -> Int -> [Constructor] -> [TypeName] -> [Function]
generateFunc seed nbp nbq cs sorts = (Function (FunName "f") [sort] sort [([Bottom], p)]) : fs
  where sort = sorts!!0
        p = generatePattern s1 cs nbp sort
        fs = generateCrossFunc s2 nbq cs sorts
        (s1, s2) = split seed

generateCrossFunc :: RandomGen g => g -> Int -> [Constructor] -> [TypeName] -> [Function]
generateCrossFunc seed nb cs sorts = map createFunc l
  where n = length sorts
        l = zip [0..] (genSeedList seed (n^2-n))
        createFunc (i, g) = Function (FunName f) [s1] s2 [([Bottom], p)]
          where (j, k) = i `divMod` (n-1)
                s1 = sorts !! j
                s2 = if k < j then (sorts !! k) else (sorts !! (k+1))
                f = "f_" ++ (show s1) ++ (show s2)
                p = generatePattern seed cs nb s2

generatePattern :: RandomGen g => g -> [Constructor] -> Int -> TypeName -> Term
generatePattern _ _ 0 _ = AVar (VarName "_") Unknown
generatePattern seed cs nb sort = Appl rC (map genSub rDistl)
  where (s1, s2) = split seed
        rC = getRandomConst seed cs (nb > 1) sort
        dom = domain (Signature cs []) rC
        ar = length dom
        rDistl = zip3 (genSeedList s1 ar) (rDistList s2 ar (nb-1)) dom
        genSub (seedi, nbi, si) = generatePattern seedi cs nbi si

generateTRS :: RandomGen g => Signature -> g -> Int -> Int -> [Rule]
generateTRS sig seed nb rules = map (genRule) (genSeedList seed rules)
  where genRule seedi = generateRule sig seedi nb

generateRule :: RandomGen g => Signature -> g -> Int -> Rule
generateRule sig seed nb = Rule lhs (generateRhs sig s2 m nb sort)
  where (s1, s2) = split seed
        lhs = generateLhs sig s1
        sort = (domain sig (FunName "f"))!!0
        m = mapVariables sig lhs sort

generateLhs :: RandomGen g => Signature -> g -> Term
generateLhs sig@(Signature cs _) seed = Appl f [Appl c xs]
  where f = FunName "f"
        c = getRandomConst seed cs True ((domain sig f)!!0)
        xs = map createVar [1..length (domain sig c)]
        createVar i = AVar (VarName ("x" ++ show i)) Unknown

generateRhs :: RandomGen g => Signature -> g -> (M.Map TypeName [VarName]) -> Int -> TypeName -> Term
generateRhs sig seed m 0 sort
  | rB              = Appl f [generateRhs sig s2 m 0 rDom]
  | M.member sort m = AVar (getRandom s2 (m M.! sort)) Unknown
  | otherwise       = Appl g [generateRhs sig s2 m 0 dom]
  where (s1,s2) = split seed
        rB = ((length m) > 1) && (rBool s1)
        dom = getRandom seed (M.keys m)
        rDom = getRandom s1 (filter (/=sort) (M.keys m))
        g = FunName ("f_" ++ (show dom) ++ (show sort))
        f = FunName ("f_" ++ (show rDom) ++ (show sort))
generateRhs sig@(Signature cs _) seed m nb sort = Appl rC (map genSub rDistl)
  where (s1, s2) = split seed
        rC = getRandomConst seed cs (nb > 1) sort
        dom = domain (Signature cs []) rC
        ar = length dom
        rDistl = zip3 (genSeedList s1 ar) (rDistList s2 ar (nb-1)) dom
        genSub (seedi, nbi, si) = generateRhs sig seedi m nbi si

mapVariables :: Signature -> Term -> TypeName -> M.Map TypeName [VarName]
mapVariables _ (AVar x _) s = M.singleton s [x]
mapVariables sig (Appl f ts) _ = M.unionsWith (++) (map mapV tSs)
  where tSs = zip ts (domain sig f)
        mapV = uncurry (mapVariables sig)

genSeedList :: RandomGen g => g -> Int -> [g]
genSeedList _ 0 = []
genSeedList seed size = ns : (genSeedList ns (size-1))
  where (_, ns) = next seed

rBool :: RandomGen g => g -> Bool
rBool seed = fst (randomR (False, True) seed)

rBoolList :: RandomGen g => g -> Int -> [Bool]
rBoolList seed size = (replicate (rI-1) False) ++ True : (replicate (size-rI) False) 
  where rI = fst (randomR (0, size-1) seed)

rDistList :: RandomGen g => g -> Int -> Int -> [Int]
rDistList s0 size nb = while s0 nb (take size (repeat 0))
  where while _ 0 l = l
        while seed n l = while next (n-1) (l1 ++ (k+1):l2)
          where (i, next) = randomR (0, size-1) seed
                (l1, k:l2) = splitAt i l

getRandomConst :: RandomGen g => g -> [Constructor] -> Bool -> TypeName -> FunName
getRandomConst seed cList b sort = getRandom seed cListS
  where cListS = mapMaybe (getConst b) cList
        getConst True (Constructor _ [] _) = Nothing
        getConst _ (Constructor c _ range) = if sort == range then Just c else Nothing

getRandom :: RandomGen g => g -> [a] -> a
getRandom seed l = l !! (fst (randomR (0, (length l) -1) seed))