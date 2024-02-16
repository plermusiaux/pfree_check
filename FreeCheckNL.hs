{-# LANGUAGE LambdaCase #-}

module FreeCheckNL ( checkTRSnl, checkPfreeNL ) where

import Control.Arrow ( left )
import Control.Monad ( foldM )

import Data.List ( isSubsequenceOf )
import Data.Either
import Data.Maybe
import Data.Traversable ( mapAccumL )

import qualified Data.Map as M
import qualified Data.Set as S

import Text.Printf ( printf )

import AlgoUtils
import Datatypes
import Signature
import Reach ( computeQc )
import ReducePattern

-------------------------------------------------------------------------------

data Cache = Cache (M.Map (Term, [Term]) Term)

emptyCache = Cache M.empty


complementC :: Signature -> Cache -> Term -> Term -> (Cache, Term)
complementC sig = comp
  where
    comp c u (AVar _ (AType _ Bottom)) = (c, Bottom)                          --M1
    comp c u Bottom = (c, u)                                                  --M2
    comp c (Plus u1 u2) t = (c2, plus p1 p2)                                  --M3
      where (c1, p1) = comp c u1 t
            (c2, p2) = comp c1 u2 t
    comp c Bottom _ = (c, Bottom)                                             --M5
    comp c p@(Appl _ _) (Plus q1 q2) = (c2, p2)                               --M6
      where (c1, p1) = comp c p q1
            (c2, p2) = comp c1 p1 q2
    comp c (Appl f ps) (Appl g qs)
      | f /= g        = (c, Appl f ps)                                        --M8
      | someUnchanged = (c', Appl f ps)
      | otherwise     = (c', sumTerm [appl f ps' | ps' <- interleave ps pqs]) --M7
      where (c', pqs) = foldr accuComp (c,[]) (zip ps qs)
            someUnchanged = or (zipWith (==) ps pqs)
    comp c u@(Appl f ts) (AVar _ (AType _ q)) = (c', plus match subMatch)     --C1
      where (cm, match) = conj c u q
            subMatch = sumTerm [appl f ps | ps <- interleave ts tqs]
            (c', tqs) = foldr accuComp (cm,[]) (zip ts (map (`buildVar` q) (domain sig f)))
    comp c (Compl v t) u = comp c v (plus t u)                                --C2
    comp c v@(AVar x sp) t = case getInstance sig c v (collect t) of
      r@(_, Bottom) -> r                                                      --C3
      (c', _)       -> (c', Compl v t) --Alias x (Compl (AVar NoName sp) t)
    comp c a@(Alias x p) t = case getInstance sig c a (collect t) of
      r@(_, Bottom) -> r                                                      --C3'
      (c', _)       -> (c', Compl a t)
    accuComp (pi, qi) (ci, ts) = (c', ti:ts)
      where (c', ti) = comp ci pi qi
    conj c u (Plus p1 p2) = (c2, plus v1 v2)                                  --S2
      where (c1, v1) = conj c u p1
            (c2, v2) = conj c1 u p2
    conj c u (AVar _ (AType _ Bottom)) = (c, u)                               --T2
    conj c (AVar x (AType s Bottom)) p                                        --T1
      | hasType sig p s = (c, alias x p)
      | otherwise       = (c, Bottom)
    conj c (Appl f ps) (Appl g qs)
      | f == g    = (c', maybe Bottom (Appl f) pXqs)                          --T3
      | otherwise = (c, Bottom)                                               --T4
      where (c', pXqs) = foldr accuConj (c, Just []) $ zip ps qs
    conj c (AVar x (AType s p)) (Appl f ts)
        | s == s'   = comp c' (alias x (maybe Bottom (Appl f) zXts)) p        --P1
        | otherwise = (c, Bottom)
        where (d, s') = sigOf sig f
              (c', zXts) = foldr accuConj (c, Just []) $ zip (map (`buildVar` p) d) ts
    conj c (Compl u t) p = comp c' v t                                        --P5
      where (c', v) = conj c u p
    conj c (Alias x u) p = (c, alias x (conjunction sig u p))                 --L4
    accuConj _ (ci, Nothing) = (ci, Nothing)
    accuConj (pi, qi) (ci, Just ts) = case conj ci pi qi of
      (c', Bottom) -> (c', Nothing)
      (c', ti)     -> (c', Just (ti:ts))

-------------------------------------------------------------------------------


-- check TRS : call checkRule for each rule and concatenate the results
-- return a map of failed rule with the terms that do not satisfy the expected pattern-free property
checkTRSnl :: Signature -> [Rule] -> IO (M.Map Rule (Term,Term))
checkTRSnl sig = fmap snd . foldM accuCheck (emptyCache, M.empty)
  where nSig = normalizeSig sig
        accuCheck (c, m) rule = do
          (c', fails) <- checkRule nSig c rule
          if null fails then return (c', m)
          else return (c', M.union m fails)

-- check rule : for each profile of the head function symbol of the left hand side,
-- alias the variables in the right hand side and build its semantics equivalent,
-- then check that the term obtained verifies the corresponding pattern-free property.
-- return a list of terms that do not satisfy the expected pattern-free properties
checkRule :: Signature -> Cache -> Rule -> IO (Cache, M.Map Rule (Term,Term))
checkRule sig = \c0 -> foldM accuCheck (c0, M.empty) . inferRules sig
  where accuCheck (c, m) (Rule lhs rhs, p) = do
          printf "checking RULE %v\n" (Rule lhs rhs)
          (c', ct) <- checkPfree sig c (rhs, p)
          case ct of
            Bottom -> return (c', m)
            _      -> return (c', M.insert (Rule lhs rhs) (p, ct) m)

-- check that a term is p-free
-- parameters: Signature, Pattern p (should be a sum of constructor patterns), Rhs term of a rule (should be a qsymb)
-- return Bottom if true, a counter-example otherwise
checkPfree :: Signature -> Cache -> (Term, Term) -> IO (Cache, Term)
checkPfree sig = \c0 -> \case
    (t0, Bottom) -> return (c0, t0)
    (t0, p0)     ->
      let checkMap = recCheck c0 (convert t0) [p0] (VarMap M.empty) in
      either (instantiate sig) (\ c _ -> (c,Bottom)) checkMap t0
        <$ printf "checking %v-free: %v\n" p0 t0
  where convert x@(AVar _ _)  = x
        convert a@(Alias _ _) = a
        convert u@(Compl _ _) = u
        convert u@(Appl f us)
          | isFunc sig f = AVar (Reduct u) (AType (range sig f) Bottom)
          | otherwise    = Appl f (map convert us)
        recCheck c _ _ BotMap = Right c
        recCheck c v@(AVar x _) pl cMap = nextF (checkInsert sig x (v, pl) (c, cMap))
        recCheck c (Alias x t) pl cMap = nextF (checkInsert sig x (t, pl) (c, cMap))
        recCheck c t@(Appl f _) pl cMap =
          let q = foldr (plus . buildVar (range sig f)) Bottom pl in
          let (c', tm) = complementC sig c t q in
          foldM (check cMap) c' (removePlusses tm)
        nextF (c, BotMap) = Right c
        nextF cm@(c, VarMap vMap) = case findReduct vMap of
          Nothing -> Left cm
          Just (x@(Reduct (Appl f ts)), u, ql) ->
            let d = domain sig f in
            let q = foldr (plus . (Appl f) . (zipWith buildVar d)) Bottom profiles
                (c1, profiles) = selectProfiles sig c f u ql in
            let (c2, tm) = complementC sig c1 (Appl f (map convert ts)) q in
            foldM (check (VarMap (M.delete x vMap))) c2 (removePlusses tm)
        check cMap c t = nextF $ getCheckMap sig t (c, cMap)

-- given the profiles of f select the combinations of profiles
-- such that for all instances v of t verifying the right-hand side,
-- there exists p in ql such that v is p-free.
-- return the left-hand sides of these combinations of profiles
selectProfiles :: Signature -> Cache -> FunName -> Term -> [Term] -> (Cache, [[Term]])
selectProfiles sig c0 f t ql = (cf, map fst oks)
  where (cf, oks, _) = getCombinations (partition c0 (profile sig f))
        getCombinations r@(_, _, []) =  r
        getCombinations (c, okl, (d,r):tail) = (cDist, recokl, (d,r):reckol)
          where (cRec, oktail, kotail) = getCombinations (c, okl, tail)
                sumProfile (d', r') = (zipWith plus d d', plus r r')
                (cDist, okdist, kodist) = partition cRec (map sumProfile kotail)
                recokl = oktail ++ okdist
                reckol = kotail ++ kodist
        partition c = foldr checkProfile (c, [], [])
        checkProfile p@(_, r) (c, okl, kol) = case foldM accuCheck c tmSet of
          Left c'  -> (c', okl, p:kol) -- profile rejected
          Right c' -> (c', p:okl, kol) -- profile accepted
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

findReduct = M.foldlWithKey getReduct Nothing
  where getReduct _ r@(Reduct _) (u, ql) = Just (r, u, ql)
        getReduct acc _ _ = acc


--------------------------------- no cache ------------------------------------


-- using a local cache seems to be more efficient than running a no cache check
checkPfreeNL :: Signature -> (Term, Term) -> IO Bool
checkPfreeNL sig = fmap (isBottom . snd) . checkPfree sig emptyCache


-------------------------------- checkInstance: -------------------------------


-- check if there exists an instance of a linear pattern that is not
-- p-free for all p in q0
checkInstance :: Signature -> Term -> [Term] -> Bool
checkInstance _ Bottom _ = False
checkInstance sig t0 q0
  | any isBottom q0 = False
  | otherwise       = isNothing (computeInstance M.empty t0 q0)
  where powerQ0 = powerConj sig q0
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
        subInstance rSub tqs = foldr computeSub Nothing tqs
          where computeSub (ti, qi) r = maybe r Just $ computeInstance rSub ti qi
--                         subInstance rSub [] = Nothing -- found instance
--                         subInstance rSub ((ti, qi):tail) = case computeInstance rSub ti qi of
--                           Nothing -> subInstance rSub tail
--                           just    -> just -- no instance found for ti and qi


getInstance :: Signature -> Cache -> Term -> [Term] -> (Cache, Term)
getInstance sig c t@Bottom _ = (c, t)
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
  where powerQ0 = powerConj sig q0
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
        getSubInstance rSub tqs = foldr computeSub (Left []) tqs
          where computeSub (ti, qi) tail = either ((`left` tail) . (:)) Right (computeInstance rSub ti qi)
--                         getSubInstance rSub [] = Left []
--                         getSubInstance rSub ((ti, qi):tail) = case computeInstance rSub ti qi of
--                           Right r' -> Right r'
--                           Left vi  -> left (vi:) (getSubInstance rSub tail)




-- return all possible distributions of qs over ts
computeQt :: [Term] -> [Term] -> [[(Term, [Term])]]
computeQt = \ts -> foldr (concatMap.distribute) [zip ts (repeat [])]
  where distribute _ [] = []
        distribute q ((t,xl):ql) = ((t, q:xl):ql):(map ((t,xl):) (distribute q ql))


-- [powerConj sig ql] return the exhaustive list of pairs (qs, t) where
-- qs is a sublist of ql and t is a not bottom conjunction of qs
powerConj :: Signature -> [Term] -> [([Term], Term)]
powerConj sig = foldr accuConj []
  where accuConj q [] = [([q], q)]
        accuConj q l0 = ([q], q):foldr (conjCons q) l0 l0
        conjCons q (ql, t) = case conjunction sig t q of
          Bottom -> id
          txq    -> ((q:ql, txq):)

-- [selectPConj sig t q0 pQ]
-- pQ must be a list of pairs (ql, x) where x is the conjunction of ql
-- and all terms of q0 in ql are in the same order (q0 and ql are 2 sublists of a bigger one)
-- return the list of pairs (qDiff, q) where qDiff is the difference q0 \ ql and
-- q is a bottom conjunction of t and x (\ie of t and ql), for each (ql, x) of pQ
-- such that ql is a subset of q0 and q is not bottom
-- used to filter conjunction not already considered and compatible with the current term
selectPConj :: Signature -> Term -> [Term] -> [([Term], Term)] -> [([Term], Term)]
selectPConj sig t q0 = foldr accuSelect [(q0, t)]
  where accuSelect (ql, q) = case checkDiff q0 ql of
          Nothing    -> id
          Just qDiff -> if isBottom txq then id else ((qDiff, txq):)
          where txq = conjunction sig t q

-- generate (as a list) the complement of p-free constructor patterns of sort s
-- with the set of terms rSet
computePatterns :: Signature -> AType -> S.Set Term -> [Term]
computePatterns sig (AType s p) = \rSet ->
    let prSet = S.union rSet (removePlusses p) in
    concatMap (buildPatterns prSet) (ctorsOfRange sig s)
  where buildPatterns pSet f =  mapMaybe buildCompl (computeQc sig f pSet)
          where buildCompl qs
                  | any isBottom xqs = Nothing
                  | otherwise = Just (Appl f xqs)
                  where xqs = zipWith (complement sig) xs (map sumTerm qs)
                xs = map (`buildVar` p) (domain sig f)

