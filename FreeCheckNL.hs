{-# LANGUAGE OverloadedStrings #-}

module FreeCheckNL ( checkTRSnl, checkPfreeNL ) where

import Control.Arrow ( left )
import Control.Monad ( foldM )

import Debug.Trace

import Data.List ( isSubsequenceOf, partition )
import Data.Either
import Data.Maybe
import qualified Data.Map as M
import qualified Data.Set as S

import AlgoUtils
import Datatypes
import Signature
import Reach ( computeQc )
import ReducePattern

-------------------------------------------------------------------------------

data Cache = Cache (M.Map (Term, [Term]) Term)

emptyCache = Cache M.empty


complementC :: Signature -> Cache -> Term -> Term -> (Cache, Term)
complementC sig c0 p1 p2 = comp c0 p1 p2
  where
    comp c u (AVar _ (AType _ Bottom)) = (c, Bottom)                      --M1
    comp c u Bottom = (c, u)                                              --M2
    comp c (Plus q1 q2) p = (c2, plus p1 p2)                              --M3
      where (c1, p1) = comp c q1 p
            (c2, p2) = comp c1 q2 p
--    (Var x) \\ p@(Appl g ps) = alias x (sum [pattern f \\ p | f <- fs])
--      where fs = ctorsOfSameRange sig g
--            pattern f = Appl f (replicate (arity sig f) (Var "_"))
    comp c Bottom _ = (c, Bottom)                                         --M5
    comp c p@(Appl _ _) (Plus q1 q2) = (c2, p2)                           --M6
      where (c1, p1) = comp c p q1
            (c2, p2) = comp c1 p1 q2
    comp c (Appl f ps) (Appl g qs)
      | f /= g        = (c, appl f ps)                                    --M8
      | someUnchanged = (c', appl f ps)
      | otherwise = (c', sumTerm [appl f ps' | ps' <- interleave ps pqs]) --M7
      where (c', pqs) = foldr accuComp (c,[]) (zip ps qs)
            someUnchanged = or (zipWith (==) ps pqs)
    comp c u@(Appl f ts) (AVar _ (AType _ q)) = (c', plus match subMatch) --C1
      where match = conjunction sig u q
            subMatch = sumTerm [appl f ps | ps <- interleave ts tqs]
            (c', tqs) = foldr accuComp (c,[]) (zip ts (map buildVar (domain sig f)))
            buildVar s = AVar NoName (AType s q)
    comp c (Compl v t) u = comp c v (plus t u)                            --C2
    comp c v@(AVar x sp) t = case getInstance sig c v (collect t) of
      r@(_, Bottom) -> r                                                  --C3
      (c', _)       -> (c', Compl v t) --Alias x (Compl (AVar NoName sp) t)
    comp c a@(Alias x p) t = case getInstance sig c a (collect t) of
      r@(_, Bottom) -> r                                                  --C3'
      (c', _)       -> (c', Compl a t)
    accuComp (pi, qi) (ci, ts) = (ci', ti:ts)
      where (ci', ti) = comp ci pi qi
--    p1 \\ Alias x p2 = p1 \\ p2


-------------------------------------------------------------------------------


-- check TRS : call checkRule for each rule and concatenate the results
-- return a map of failed rule with the terms that do not satisfy the expected pattern-free property
checkTRSnl :: Signature -> [Rule] -> M.Map Rule (Term,Term)
checkTRSnl sig rules = snd (foldl accuCheck (emptyCache, M.empty) rules)
  where nSig = normalizeSig sig
        accuCheck (c, m) rule
          | null fails = (c', m)
          | otherwise  = (c', M.union m fails)
          where (c', fails) = checkRule nSig c rule

-- check rule : for each profile of the head function symbol of the left hand side,
-- alias the variables in the right hand side and build its semantics equivalent,
-- then check that the term obtained verifies the corresponding pattern-free property.
-- return a list of terms that do not satisfy the expected pattern-free properties
checkRule :: Signature -> Cache -> Rule -> (Cache, M.Map Rule (Term,Term))
checkRule sig c0 r@(Rule (Appl f _) _) = foldl accuCheck (c0, M.empty) rules
  where accuCheck (c, m) (Rule lhs rhs, p)
          | isBottom ct = (c', m)
          | otherwise   = (c', M.insert (Rule lhs rhs) (p, ct) m)
          where (c', ct) = trace ("checking RULE " ++ show (Rule lhs rhs)) $ checkPfree sig c (rhs, p)
        rules = concatMap buildRule (map buildDomain (profile sig f))
        buildRule (_, Bottom) = []
        buildRule (ad, p) = zip (replaceVariables sig r ad) (repeat p)
        buildDomain (qs, p) = (zipWith AType d qs, p)
        d = domain sig f

-- check that a term is p-free
-- parameters: Signature, Pattern p (should be a sum of constructor patterns), Rhs term of a rule (should be a qsymb)
-- return Bottom if true, a counter-example otherwise
checkPfree :: Signature -> Cache -> (Term, Term) -> (Cache, Term)
checkPfree _ c0 (t0, Bottom) = (c0, t0)
checkPfree sig c0 (t0, p0) = trace ("checking " ++ show p0 ++ "-free: " ++ show t0) $ instantiate sig checkMap t0
  where checkMap = either id (\c -> (c, BotMap)) $ recCheck c0 t0 [p0] (VarMap M.empty) S.empty
        convert fSet x@(AVar _ _)  = (fSet, x)
        convert fSet a@(Alias _ _) = (fSet, a)
        convert fSet u@(Compl _ _) = (fSet, u)
        convert fSet u@(Appl f us)
          | isFunc sig f = (S.insert u fSet, v)
          | otherwise    = (fSet', Appl f vs)
          where (fSet', vs) = foldr accuConvert (fSet, []) us
                v = AVar (VarName (show u)) (AType (range sig f) Bottom)
        accuConvert ti (mi, tl) = (mi', ti':tl)
          where (mi', ti') = convert mi ti
        recCheck c _ _ BotMap _ = Right c
        recCheck c v@(AVar x _) pl cMap fSet = nextF fSet (checkInsert sig x (v, pl) (c, cMap))
        recCheck c (Alias x t) pl cMap fSet = nextF fSet (checkInsert sig x (t, pl) (c, cMap))
        recCheck c t@(Appl f ts) pl cMap@(VarMap vMap) fSet = foldM check c' (removePlusses tm)
          where check cc ti = nextF fSet' $ getCheckMap sig ti (cc, cMap)
                (fSet', ts') = foldr accuConvert (fSet, []) ts
                (c', tm) = complementC sig cq (Appl f ts') (sumTerm ql)
                  where (cq, ql)
                          | isFunc sig f = (cp, map ((Appl f) . (zipWith buildVar d)) profiles)
                          | otherwise    = (c, zipWith (flip buildVar) pl (repeat s))
                          where s = range sig f
                                d = domain sig f
                                buildVar si qi = AVar NoName (AType si qi)
                                (cp, profiles) = selectProfiles sig c f u pl'
                                (u, pl') = case M.lookup (VarName (show t)) vMap of
                                  Just (v, ql) -> (v, pl++ql)
                                  Nothing -> (AVar NoName (AType s Bottom), pl)
        nextF _ (c, BotMap) = Right c
        nextF fSet (c, cMap) = case S.maxView fSet of
          Nothing          -> Left (c, cMap)
          Just (tf, fSet') -> recCheck c tf [] cMap fSet'

selectProfiles :: Signature -> Cache -> FunName -> Term -> [Term] -> (Cache, [[Term]])
selectProfiles sig c0 f t ql = (cf, map fst oks)
  where (cf, (oks, _)) = getCombinations (partition c0 (profile sig f))
        getCombinations r@(_, (_, [])) =  r
        getCombinations (c, (okl, (d,r):tail)) = (c', (recokl, (d,r):reckol))
          where (c', recokl, reckol) = case getCombinations (c, (okl, tail)) of
                  (cRec, (oktail, kotail)) -> (cDist, oktail ++ okdist, kotail ++ kodist)
                    where (cDist, (okdist, kodist)) = partition cRec (map sumProfile kotail)
                sumProfile (d', r') = (zipWith plus d d', plus r r')
        partition c = foldr checkProfile (c, ([], []))
        checkProfile p@(_, r) (c, (okl, kol)) = case foldM accuCheck c tmSet of
          Left c'  -> (c', (okl, p:kol)) -- profile rejected
          Right c' -> (c', (p:okl, kol)) -- profile accepted
          where tmSet = removePlusses (conjunction sig t (AVar NoName (AType s r)))
        accuCheck c u = case getInstance sig c u ql of
          (c', Bottom) -> Right c'
          (c', _)      -> Left c' -- profile rejected, stop computation
        s = range sig f


------------------------------ check Variables: -------------------------------


data CheckMap = VarMap (M.Map VarName (Term, [Term]))
              | BotMap


instantiate :: Signature -> (Cache, CheckMap) -> Term -> (Cache, Term)
instantiate _ (c, BotMap) _ = (c, Bottom)
instantiate sig (c, VarMap vMap) (AVar x _) = getInstance sig c t q
  where (t, q) = vMap M.! x
instantiate sig (c, VarMap vMap) (Alias x _) = getInstance sig c t q
  where (t, q) = vMap M.! x
instantiate sig r@(c, cMap) (Appl f ts) = (c, Appl f (map (snd.(instantiate sig r)) ts))


checkInsert :: Signature -> VarName -> (Term, [Term]) -> (Cache, CheckMap) -> (Cache, CheckMap)
checkInsert _ _ _ r@(_, BotMap) = r
checkInsert sig x tq@(AVar _ _, q0) (c, VarMap vMap) = case getInstance sig c t' q' of
  (c', Bottom)  -> (c', BotMap)
  (c', _)       -> (c', VarMap vMap')
  where ((t', q'), vMap') = case M.insertLookupWithKey glue x tq vMap of
          (Nothing    , rMap) -> (tq, rMap)
          (Just (t, q), rMap) -> ((t, q++q0), rMap)
        glue _ _ (t, q) = (t, q++q0)
checkInsert sig x (t0, q0) (c, VarMap vMap) = case getInstance sig c t' q' of
  (c', Bottom) -> (c', BotMap)
  (c', _)      -> (c', VarMap (M.insert x (t', q') vMap))
  where (t', q') = case M.lookup x vMap of
                     Nothing -> (t0, q0)
                     Just (t, q) -> (conjunction sig t0 t, q++q0)

getCheckMap :: Signature -> Term -> (Cache, CheckMap) -> (Cache, CheckMap)
getCheckMap _ _ r@(_, BotMap) = r
getCheckMap _ (AVar NoName _) r = r
getCheckMap _ (Compl (AVar NoName _) _) r = r
getCheckMap sig (Appl f ts) r = foldr (getCheckMap sig) r ts
getCheckMap sig v@(AVar x _) r = checkInsert sig x (v, []) r
getCheckMap sig (Alias x u) r = checkInsert sig x (u, []) r
getCheckMap sig (Compl (Alias x u) q) r = checkInsert sig x (u, collect q) r
getCheckMap sig (Compl v@(AVar x _) q) r = checkInsert sig x (v, collect q) r



--------------------------------- no cache ------------------------------------


checkPfreeNL :: Signature -> (Term, Term) -> Bool
checkPfreeNL sig = isBottom . snd . (checkPfree sig emptyCache)

-- complementA :: Signature -> Term -> Term -> Term
-- complementA sig p1 p2 = p1 \\ p2
--   where
--     u \\ (AVar _ (AType _ Bottom)) = Bottom                               --M1
--     u \\ Bottom = u                                                       --M2
--     Plus q1 q2 \\ p = plus (q1 \\ p) (q2 \\ p)                            --M3
-- --    (Var x) \\ p@(Appl g ps) = alias x (sum [pattern f \\ p | f <- fs])
-- --      where fs = ctorsOfSameRange sig g
-- --            pattern f = Appl f (replicate (arity sig f) (Var "_"))
--     Bottom \\ u = Bottom                                                  --M5
--     p@(Appl _ _) \\ (Plus p1 p2) = (p \\ p1) \\ p2                        --M6
--     Appl f ps \\ Appl g qs
--         | f /= g || someUnchanged = appl f ps                             --M8
--         | otherwise = sumTerm [appl f ps' | ps' <- interleave ps pqs]     --M7
--       where pqs = zipWith (\\) ps qs
--             someUnchanged = or (zipWith (==) ps pqs)
--     u@(Appl f ts) \\ (AVar _ (AType _ q)) = plus match subMatch           --C1
--       where match = conjunction sig u q
--             subMatch = sumTerm [appl f ps | ps <- interleave ts tqs]
--             tqs = zipWith (\\) ts (map buildVar (domain sig f))
--             buildVar s = AVar NoName (AType s q)
--     (Compl v t) \\ u = v \\ (plus t u)                                    --C2
--     v@(AVar x sp) \\ t
--         | checkInstance sig v ql = Compl v t --Alias x (Compl (AVar NoName sp) t)
--         | otherwise              = Bottom                                 --C3
--         where ql = collect t
--     a@(Alias x p) \\ t
--         | checkInstance sig p ql = Compl (Alias x p) t
--         | otherwise              = Bottom                                 --C3'
--         where ql = collect t
-- --    p1 \\ Alias x p2 = p1 \\ p2
--
--
-- -- check that a term is p-free
-- -- parameters: Signature, Pattern p (should be a sum of constructor patterns), Rhs term of a rule (should be a qsymb)
-- -- return a list of terms that do not satisfy the expected pattern-free property
-- checkPfreeNL :: Signature -> (Term, Term) -> Bool
-- checkPfreeNL _ (_, Bottom) = True
-- checkPfreeNL sig (t0, p0) = trace ("checking " ++ show p0 ++ "-free: " ++ show t0) (recCheck t0 [p0] (VarMap M.empty) S.empty)
--   where convert fSet x@(AVar _ _)  = (fSet, x)
--         convert fSet a@(Alias _ _) = (fSet, a)
--         convert fSet u@(Compl _ _) = (fSet, u)
--         convert fSet u@(Appl f us)
--           | isFunc sig f = (S.insert u fSet, v)
--           | otherwise    = (fSet', Appl f vs)
--           where (fSet', vs) = foldr accuConvert (fSet, []) us
--                 v = AVar (VarName (show u)) (AType (range sig f) Bottom)
--         accuConvert ti (mi, tl) = (mi', ti':tl)
--           where (mi', ti') = convert mi ti
--         recCheck _ _ BotMap _ = True
--         recCheck v@(AVar x _) pl cMap fSet = nextF fSet (checkVar sig x (v, pl) cMap)
--         recCheck (Alias x t) pl cMap fSet = nextF fSet (checkVar sig x (t, pl) cMap)
--         recCheck t@(Appl f ts) pl cMap@(VarMap vMap) fSet = all ((checkNextF fSet') . (getCheckMap sig cMap)) tmSet
--           where (fSet', ts') = foldr accuConvert (fSet, []) ts
--                 tmSet = removePlusses (complementA sig (Appl f ts') (sumTerm cl))
--                   where cl | isFunc sig f = map ((Appl f) . (zipWith buildVar d)) profiles
--                            | otherwise    = zipWith (flip buildVar) pl (repeat s)
--                            where s = range sig f
--                                  d = domain sig f
--                                  buildVar si qi = AVar NoName (AType si qi)
--                                  profiles = selectProf sig f u pl'
--                                  (u, pl') = case M.lookup (VarName (show t)) vMap of
--                                    Just (v, ql) -> (v, pl++ql)
--                                    Nothing -> (AVar NoName (AType s Bottom), pl)
--         nextF _ BotMap = True
--         nextF fSet cMap = case S.maxView fSet of
--           Nothing          -> False
--           Just (tf, fSet') -> recCheck tf [] cMap fSet'
--         checkNextF fSet cMap
--           | isBotMap cMap = True
--           | otherwise     = case S.maxView fSet of
--                               Nothing          -> False
--                               Just (tf, fSet') -> recCheck tf [] cMap fSet'
--
-- selectProf :: Signature -> FunName -> Term -> [Term] -> [[Term]]
-- selectProf sig f t ql = map fst (fst (getCombinations part))
--   where part = partition checkProfile (profile sig f)
--         getCombinations (okl, []) =  (okl, [])
--         getCombinations (okl, ((d,r):tail)) = (recokl, (d,r):reckol)
--           where (recokl, reckol) = case getCombinations (okl, tail) of
--                   (oktail, kotail) -> (oktail ++ okdist, kotail ++ kodist)
--                     where (okdist, kodist) = partition checkProfile (map sumProfile kotail)
--                 sumProfile (d', r') = (zipWith plus d d', plus r r')
--         checkProfile (_, r) = all checkRange (removePlusses (conjunction sig t (AVar NoName (AType s r))))
--         checkRange u = not (checkInstance sig u ql)
--         s = range sig f
--
--
-- checkGlue :: Signature -> (Term, [Term]) -> (Term, [Term]) -> (Term, [Term])
-- checkGlue _ (Bottom, _) (_, _) = (Bottom, [])
-- checkGlue _ (_, _) (Bottom, _) = (Bottom, [])
-- checkGlue sig (AVar _ _, q1) (t2, q2)
--   | checkInstance sig t2 ql = (t2, ql)
--   | otherwise               = (Bottom, [])
--   where ql = q1 ++ q2
-- checkGlue sig (t1, q1) (AVar _ _, q2)
--   | checkInstance sig t1 ql = (t1, ql)
--   | otherwise               = (Bottom, [])
--   where ql = q1 ++ q2
-- checkGlue sig (t1, q1) (t2, q2)
--   | checkInstance sig txt ql = (txt, ql)
--   | otherwise                = (Bottom, [])
--   where txt = conjunction sig t1 t2
--         ql = q1 ++ q2
--
-- checkVar :: Signature -> VarName -> (Term, [Term]) -> CheckMap -> CheckMap
-- checkVar _ _ _ BotMap = BotMap
-- checkVar sig x tq@(AVar _ _, q0) (VarMap vMap)
--   | checkInstance sig t' q' = VarMap vMap'
--   | otherwise               = BotMap
--   where ((t', q'), vMap') = case M.insertLookupWithKey glue x tq vMap of
--           (Nothing    , rMap) -> (tq, rMap)
--           (Just (t, q), rMap) -> ((t, q++q0), rMap)
--         glue _ _ (t, q) = (t, q++q0)
-- checkVar sig x (t0, q0) (VarMap vMap)
--   | checkInstance sig t' q' = VarMap (M.insert x (t', q') vMap)
--   | otherwise               = BotMap
--   where (t', q') = case M.lookup x vMap of
--                      Nothing -> (t0, q0)
--                      Just (t, q) -> (conjunction sig t0 t, q++q0)
--
-- getCheckMap :: Signature -> CheckMap -> Term -> CheckMap
-- getCheckMap _ BotMap _ = BotMap
-- getCheckMap _ cMap (AVar NoName _) = cMap
-- getCheckMap _ cMap (Compl (AVar NoName _) _) = cMap
-- getCheckMap sig cMap (Appl f ts) = foldl (getCheckMap sig) cMap ts
-- getCheckMap sig (VarMap vMap) t = VarMap m
--   where m = case t of
--               AVar x _             -> M.insertWith (checkGlue sig) x (t, []) vMap
--               Alias x u            -> M.insertWith (checkGlue sig) x (u, []) vMap
--               Compl (Alias x u) q  -> M.insertWith (checkGlue sig) x (u, collect q) vMap
--               Compl v@(AVar x _) q -> M.insertWith (checkGlue sig) x (v, collect q) vMap




-------------------------------- checkInstance: -------------------------------




-- check if there exists an instance of a linear pattern that is not
-- p-free for all p in q0
checkInstance :: Signature -> Term -> [Term] -> Bool
checkInstance _ Bottom _ = False
checkInstance sig t0 q0
  | any isBottom q0 = False
  | otherwise       = isNothing (computeInstance M.empty t0 q0)
  where powerQ0 = foldr (powerConj sig) [] q0
        computeInstance reach Bottom _ = Just reach
        computeInstance reach t [] = Nothing
        computeInstance reach t q = case M.lookup t' reach of
          Nothing -> foldM conjInstance subReach powerQ
          Just q' | isSubsequenceOf q' q -> Just reach
                  | otherwise            -> foldM conjInstance subReach powerQ
          where t' = linearize t
                powerQ = selectPConj sig t' q powerQ0
                subReach = M.insert t' q reach
                conjInstance rConj (qDiff, qConj) = foldM recInstance rConj (removePlusses qConj)
                  where recInstance rRec ct@(Appl _ [])
                          | null qDiff = Nothing
                          | otherwise  = Just rRec
                        recInstance rRec (Alias _ r) = recInstance rRec r
                        recInstance rRec (AVar _ s) = foldM recInstance rRec (computePatterns sig s S.empty)
                        recInstance rRec (Compl (AVar _ s) r) = foldM recInstance rRec (computePatterns sig s (removePlusses r))
                        recInstance rRec (Appl f ts) = foldM subInstance rRec (computeQt ts qDiff)
                        subInstance rSub [] = Nothing -- found instance
                        subInstance rSub ((ti, qi):tail) = case computeInstance rSub ti qi of
                          Nothing -> subInstance rSub tail
                          just    -> just -- no instance found for ti and qi



getInstance :: Signature -> Cache -> Term -> [Term] -> (Cache, Term)
getInstance _ c Bottom _ = (c, Bottom)
getInstance sig c@(Cache m) t q
  | any isBottom q = (c, Bottom)
  | otherwise      = case M.lookup (t', q) m of
    Just r  -> (c, r)
    Nothing -> (Cache (M.insert (t',q) r m), r)
                 where r = getInst sig t' q
    where t' = linearize t


-- get an instance of a linear pattern t0 that is not p-free
-- for all p in q0, return Bottom if no such instance exists
getInst :: Signature -> Term -> [Term] -> Term
getInst sig t0 q0 = case computeInstance M.empty t0 q0 of
  Left res -> res
  _        -> Bottom
  where powerQ0 = foldr (powerConj sig) [] q0
        computeInstance reach Bottom _ = Right reach
        computeInstance reach t [] = Left t
        computeInstance reach t q = case M.lookup t' reach of
          Nothing -> foldM getConjInstance subReach powerQ
          Just q' | isSubsequenceOf q' q -> Right reach
                  | otherwise            -> foldM getConjInstance subReach powerQ
          where t' = linearize t
                powerQ = selectPConj sig t' q powerQ0
                subReach = M.insert t' q reach
                getConjInstance rConj (qDiff, qConj) = foldM getRecInstance rConj (removePlusses qConj)
                  where getRecInstance rRec ct@(Appl _ [])
                          | null qDiff = Left ct
                          | otherwise  = Right rRec
                        getRecInstance rRec (Alias _ r) = getRecInstance rRec r
                        getRecInstance rRec (AVar _ s) = foldM getRecInstance rRec (computePatterns sig s S.empty)
                        getRecInstance rRec (Compl (AVar _ s) r) = foldM getRecInstance rRec (computePatterns sig s (removePlusses r))
                        getRecInstance rRec (Appl f ts) = foldM buildf rRec (computeQt ts qDiff)
                          where buildf rAppl tqs = left (Appl f) (getSubInstance rAppl tqs)
                        getSubInstance rSub ((ti, qi):[]) = left (\vi -> [vi]) (computeInstance rSub ti qi)
                        getSubInstance rSub ((ti, qi):tail) = case computeInstance rSub ti qi of
                          Right r' -> Right r'
                          Left vi  -> left (vi:) (getSubInstance rSub tail)





computeQt :: [Term] -> [Term] -> [[(Term, [Term])]]
computeQt ts qs = foldr getDist [zip ts (repeat [])] qs
  where getDist q tQ = concatMap distribute tQ
          where distribute [] = []
                distribute ((t,xl):ql) = ((t, q:xl):ql):(map ((t,xl):) (distribute ql))

-- powerConj :: Signature -> Term -> [([Term], Term)] -> [([Term], Term)]
-- powerConj sig q l0 = foldr accuConj (map distribute l0) l0
--   where accuConj (ql, t) l
--           | isBottom txq = l
--           | otherwise    = (ql, txq):l
--           where txq = conjunction sig t q
--         distribute (ql, t) = (q:ql, t)

powerConj :: Signature -> Term -> [([Term], Term)] -> [([Term], Term)]
powerConj _ q [] = [([q], q)]
powerConj sig q l0 = foldr accuConj l0 l0
  where accuConj (ql, t) l
          | isBottom txq = l
          | otherwise    = (q:ql, txq):l
          where txq = conjunction sig t q

selectPConj :: Signature -> Term -> [Term] -> [([Term], Term)] -> [([Term], Term)]
selectPConj sig t q0 pQ = foldr accuSelect [(q0, t)] pQ
  where checkDiff [] l = Just l
        checkDiff _ [] = Nothing
        checkDiff (q1:l1) (q2:l2)
          | q1 == q2  = checkDiff l1 l2
          | otherwise = fmap (q2:) (checkDiff (q1:l1) l2)
        accuSelect (ql, q) l = case checkDiff ql q0 of
          Nothing    -> l
          Just qDiff -> if isBottom txq then l else (qDiff, txq):l
          where txq = conjunction sig t q

computePatterns :: Signature -> AType -> S.Set Term -> [Term]
computePatterns sig (AType s p) rSet = concatMap buildPatterns (ctorsOfRange sig s)
  where prSet = S.union rSet (removePlusses p)
        buildPatterns f =  mapMaybe buildCompl (computeQc sig f prSet)
          where buildCompl qs
                  | any isBottom xqs = Nothing
                  | otherwise = Just (Appl f xqs)
                  where xqs = zipWith (complement sig) xs (map sumTerm qs)
                xs = map buildVar (domain sig f)
                buildVar si = AVar NoName (AType si p)


