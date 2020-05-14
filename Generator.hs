module Generator (generate, generateBlankSig, generateP) where

import Datatypes
import Signature

import qualified Data.Map as M
import System.Random

generateBlankSig :: Int -> Int -> Signature
generateBlankSig ar nb = Signature constructors []
  where constructors = concatMap (generateConst ar sorts) sorts
        sorts = [ TypeName ("s" ++ (show i)) | i <- [1..nb] ]

generateP :: RandomGen g => g -> [Constructor] -> Int -> Term
generateP _ _ 0 = AVar (VarName "_") Unknown
generateP seed cs d = Appl rC (map genSub rBsl)
  where (s1, s2) = split seed
        Constructor rC _ _ = getRandom seed cs
        dom = domain (Signature cs []) rC
        ar = length dom
        rBsl = zip3 (genSeedList seed ar) (rBoolList s2 ar) dom
        genSub (seedi, bi, si) = generatePattern seedi cs (d-1) bi si

generate :: RandomGen g => g -> Int -> Int -> Int -> Module
generate seed ar d rules = Module sig (generateTRS sig s2 (d`div`2) rules)
  where (s1, s2) = split seed
        sig = generateSig s1 ar d

generateSig :: RandomGen g => g -> Int -> Int -> Signature
generateSig seed ar d = Signature constructors functions 
  where sorts = [ TypeName ("s" ++ (show i)) | i <- [1..nb] ]
        constructors = concatMap (generateConst ar sorts) sorts
        functions = generateFunc seed d constructors sorts
        nb = 2

generateConst :: Int -> [TypeName] -> TypeName -> [Constructor]
generateConst ar sorts range@(TypeName s) = map createConst [1..nb^ar]
  where nb = length sorts
        createConst i = Constructor name domain range
          where name = FunName ("c" ++ (show i) ++ "_" ++ s)
                domain = generateDomain ar (i-1) sorts

generateDomain :: Int -> Int -> [TypeName] -> [TypeName]
generateDomain ar i sorts = map (sorts!!) (map f [1..ar])
  where f k = (i `mod` (nb^k)) `div` (nb^(k-1))
        nb = length sorts

generateFunc :: RandomGen g => g -> Int -> [Constructor] -> [TypeName] -> [Function]
generateFunc seed d cs sorts = (Function (FunName "f") [AType sort Bottom] (AType sort p)) : fs
  where sort = sorts!!0
        p = generatePattern seed cs d True sort
        fs = generateCrossFunc seed (2*d`div`3) cs sorts

generateCrossFunc :: RandomGen g => g -> Int -> [Constructor] -> [TypeName] -> [Function]
generateCrossFunc seed d cs sorts = map createFunc l
  where n = length sorts
        l = zip [0..] (genSeedList seed (n^2-n))
        createFunc (i, g) = Function (FunName f) [AType s1 Bottom] (AType s2 p)
          where (j, k) = i `divMod` (n-1)
                s1 = sorts !! j
                s2 = if k < j then (sorts !! k) else (sorts !! (k+1))
                f = "f_" ++ (show s1) ++ (show s2)
                p = generatePattern seed cs d True s2

generatePattern :: RandomGen g => g -> [Constructor] -> Int -> Bool -> TypeName -> Term
generatePattern _ _ 0 _ _ = AVar (VarName "_") Unknown
generatePattern seed cs d b sort
  | b          = Appl rC (map genSub rBsl)
  | rBool seed = Appl rC (map genSub bsl)
  | otherwise  = AVar (VarName "_") Unknown
  where (s1, s2) = split seed
        rC = getRandomConst s1 cs sort
        dom = domain (Signature cs []) rC
        ar = length dom
        rBsl = zip3 (genSeedList seed ar) (rBoolList s2 ar) dom
        bsl = zip3 (genSeedList seed ar) (replicate ar False) dom
        genSub (seedi, bi, si) = generatePattern seedi cs (d-1) bi si

generateTRS :: RandomGen g => Signature -> g -> Int -> Int -> [Rule]
generateTRS sig seed d rules = map (genRule) (genSeedList seed rules)
  where genRule seedi = generateRule sig seedi d

generateRule :: RandomGen g => Signature -> g -> Int -> Rule
generateRule sig seed d = Rule lhs (generateRhs sig s2 m d True sort)
  where (s1, s2) = split seed
        lhs = generateLhs sig s1
        sort = (domain sig (FunName "f"))!!0
        m = mapVariables sig lhs sort

generateLhs :: RandomGen g => Signature -> g -> Term
generateLhs sig@(Signature cs _) seed = Appl f [Appl c xs]
  where f = FunName "f"
        c = getRandomConst seed cs ((domain sig f)!!0)
        xs = map createVar [1..length (domain sig c)]
        createVar i = AVar (VarName ("x" ++ show i)) Unknown

generateRhs :: RandomGen g => Signature -> g -> (M.Map TypeName [VarName]) -> Int -> Bool -> TypeName -> Term
generateRhs sig seed m 0 b sort
  | rB              = Appl f [generateRhs sig s2 m 0 False rDom]
  | M.member sort m = AVar (getRandom s2 (m M.! sort)) Unknown
  | otherwise       = Appl g [generateRhs sig s2 m 0 False dom]
  where (s1,s2) = split seed
        rB = b && ((length m) > 1) && (rBool s1)
        dom = getRandom seed (M.keys m)
        rDom = getRandom s1 (filter (/=sort) (M.keys m))
        g = FunName ("f_" ++ (show dom) ++ (show sort))
        f = FunName ("f_" ++ (show rDom) ++ (show sort))
generateRhs sig@(Signature cs _) seed m d b sort
  | b         = Appl rC (map genSub rBsl)
  | rBool s2  = Appl rC (map genSub bsl)
  | otherwise = generateRhs sig s1 m 0 True sort
  where (s1, s2) = split seed
        rC = getRandomConst s1 cs sort
        dom = domain (Signature cs []) rC
        ar = length dom
        rBsl = zip3 (genSeedList seed ar) (rBoolList s2 ar) dom
        bsl = zip3 (genSeedList seed ar) (replicate ar False) dom
        genSub (seedi, bi, si) = generateRhs sig seedi m (d-1) (bi || (d == 1)) si

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

getRandomConst :: RandomGen g => g -> [Constructor] -> TypeName -> FunName
getRandomConst seed cList sort = getRandom seed cListS
  where cListS = ctorsOfRange (Signature cList []) sort

getRandom :: RandomGen g => g -> [a] -> a
getRandom seed l = l !! (fst (randomR (0, (length l) -1) seed))
