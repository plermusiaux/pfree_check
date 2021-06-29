{-# LANGUAGE OverloadedStrings #-}

module FreeCheck (checkTRS) where

import Debug.Trace
import Data.List ( isSubsequenceOf, partition, (\\) )
import Data.Maybe
import qualified Data.Map as M
import qualified Data.Set as S
import Datatypes
import Signature

--------------------------------- From Algo: ----------------------------------

isBottom :: Term -> Bool
isBottom Bottom = True
isBottom _ = False

collect :: Term -> [Term]
collect (AVar _ (AType s p)) = [p]
collect (Plus t1 t2) = (collect t1) ++ (collect t2)

-- interleave abc ABC = Abc, aBc, abC
interleave :: [a] -> [a] -> [[a]]
interleave [] [] = []
interleave (xi:xs) (yi:ys) = (yi:xs) : (map (xi:) (interleave xs ys))

alias :: VarName -> Term -> Term
alias NoName t = t
alias x Bottom = Bottom
alias x t = Alias x t

plus :: Term -> Term -> Term
plus Bottom u = u                                                         --A1
plus t Bottom = t                                                         --A2
plus t u = Plus t u

sumTerm :: Foldable t => t Term -> Term
sumTerm = foldr plus Bottom

appl :: FunName -> [Term] -> Term
appl f ps | any isBottom ps = Bottom                                      --E1
          | otherwise = Appl f ps

removePlusses :: Term -> S.Set Term
removePlusses (Plus p1 p2) = removePlusses p1 `S.union` removePlusses p2
removePlusses (Appl f ps) = S.map (Appl f) subterms                       --S1
  where subterms = foldl buildSet (S.singleton []) (reverse ps)
        buildSet sl t = foldr (S.union . (buildList t)) S.empty sl
        buildList t l = S.map (:l) (removePlusses t)
removePlusses Bottom = S.empty
removePlusses v@(AVar _ _) = S.singleton v
removePlusses m@(Compl _ _) = S.singleton m
removePlusses a@(Alias x p) = S.map (Alias x) (removePlusses p)

complementR :: Signature -> Term -> Term -> Term
complementR sig p1 p2 = p1 \\ p2
  where
    u \\ (AVar _ _) = Bottom                                              --M1
    u \\ Bottom = u                                                       --M2
    Plus q1 q2 \\ p = plus (q1 \\ p) (q2 \\ p)                            --M3
--    (Var x) \\ p@(Appl g ps) = alias x (sum [pattern f \\ p | f <- fs])
--      where fs = ctorsOfSameRange sig g
--            pattern f = Appl f (replicate (arity sig f) (Var "_"))
    Bottom \\ u = Bottom                                                  --M5
    p@(Appl _ _) \\ (Plus p1 p2) = (p \\ p1) \\ p2                        --M6
    Appl f ps \\ Appl g qs
        | f /= g || someUnchanged = appl f ps                             --M8
        | otherwise = sumTerm [appl f ps' | ps' <- interleave ps pqs]     --M7
      where pqs = zipWith (\\) ps qs
            someUnchanged = or (zipWith (==) ps pqs)
    (Compl v t) \\ u = v \\ (plus t u)                                    --P6
    v@(AVar x sp@(AType s p)) \\ t
        | isBottom p               = sumTerm [pattern c \\ t | c <- cs]
        | isInstantiable sig s p r = alias x (Compl (AVar NoName sp) t)
        | otherwise                = Bottom                               --P7
        where cs = ctorsOfRange sig s
              pattern c = Appl c (map buildVar (domain sig c))
              buildVar si = AVar NoName (AType si p)
              r = removePlusses t
    Alias x p1 \\ p2 = alias x (p1 \\ p2)
--    p1 \\ Alias x p2 = p1 \\ p2

complementA :: Signature -> Term -> Term -> Term
complementA sig p1 p2 = p1 \\ p2
  where
    u \\ (AVar _ (AType _ Bottom)) = Bottom                               --M1
    u \\ Bottom = u                                                       --M2
    Plus q1 q2 \\ p = plus (q1 \\ p) (q2 \\ p)                            --M3
--    (Var x) \\ p@(Appl g ps) = alias x (sum [pattern f \\ p | f <- fs])
--      where fs = ctorsOfSameRange sig g
--            pattern f = Appl f (replicate (arity sig f) (Var "_"))
    Bottom \\ u = Bottom                                                  --M5
    p@(Appl _ _) \\ (Plus p1 p2) = (p \\ p1) \\ p2                        --M6
    Appl f ps \\ Appl g qs
        | f /= g || someUnchanged = appl f ps                             --M8
        | otherwise = sumTerm [appl f ps' | ps' <- interleave ps pqs]     --M7
      where pqs = zipWith (\\) ps qs
            someUnchanged = or (zipWith (==) ps pqs)
    u@(Appl f ts) \\ (AVar _ (AType _ q)) = plus match subMatch           --C1
      where match = conjunction sig u q
            subMatch = sumTerm [appl f ps | ps <- interleave ts tqs]
            tqs = zipWith (\\) ts (map buildVar (domain sig f))
            buildVar s = AVar NoName (AType s q)
    (Compl v t) \\ u = v \\ (plus t u)                                    --C2
    v@(AVar x sp) \\ t
        | checkInstance sig v ql = Compl v t --Alias x (Compl (AVar NoName sp) t)
        | otherwise              = Bottom                                 --C3
        where ql = collect t
    a@(Alias x p) \\ t
        | checkInstance sig p ql = Compl (Alias x p) t
        | otherwise              = Bottom                                 --C3'
        where ql = collect t
--    p1 \\ Alias x p2 = p1 \\ p2

-------------------------------------------------------------------------------

conjunction :: Signature -> Term -> Term -> Term
conjunction sig p1 p2 = p1 * p2
  where 
    Bottom * u = Bottom                                                   --E2
    u * Bottom = Bottom                                                   --E3
    (Plus u1 u2) * u = plus (u1 * u) (u2 * u)                             --S2
    u * (Plus u1 u2) = plus (u * u1) (u * u2)                             --S3
    v@(AVar x aType) * (AVar y (AType s2 p2)) = case aType of             --Generalization of T1/T2 for variables
        Unknown -> Alias x (AVar NoName (AType s2 p2)) -- for variable inference only
        AType s1 p1
          | s1 /= s2     -> Bottom
          | p1 == p2     -> v
          | p1 == Bottom -> AVar x (AType s2 p2)
          | p2 == Bottom -> v
--          | otherwise    -> (AVar x (AType s1 (Plus p1 p2)))
-- This should never happen, check isInstantiable sig s1 (plus p1 p2) S.empty, if it does...
    u * (AVar _ (AType s Bottom)) = u                                     --T1
    (AVar x (AType s Bottom)) * u
        | hasType sig u s = alias x u                                     --T2
        | otherwise       = Bottom
    Appl f ps * Appl g qs
        | f == g = appl f (zipWith (*) ps qs)                             --T3
        | otherwise = Bottom                                              --T4
--    (AVar _ (AType s p)) * t@(Appl f ts)
--        | s == range sig f = (sumTerm (map pattern fs)) * (complement sig q p) --P1
--        | otherwise        = Bottom
--        where fs = ctorsOfRange sig s
--              pattern a = Appl a (map buildVar (domain sig a))
--              buildVar si = AVar "_" (AType si p)
    (AVar x (AType s p)) * (Appl f ts)
        | s == range sig f = complementR sig (alias x (Appl f zXts)) p    --P1
        | otherwise        = Bottom
        where zXts = zipWith conjVar (domain sig f) ts
              conjVar si t = (AVar NoName (AType si p)) * t
    (Appl f ts) * (AVar x (AType s p))
        | s == range sig f = complementR sig (Appl f tXzs) p              --P2
        | otherwise        = Bottom
        where tXzs = zipWith conjVar ts (domain sig f)
              conjVar t si = t * (AVar NoName (AType si p))
    v1 * (Compl v2 t) = complementR sig (v1 * v2) t                       --P3-4
    (Compl v t) * u = complementR sig (v * u) t                           --P5
--    (Var x) * u = Alias x u
--    (Appl f ts) * (AVar _ (AType _ p)) = complement sig (Appl f tsXz) p
--        where tsXz = zipWith conjVar ts (domain sig f)
--              conjVar t s = t * (AVar (VarName (show t)) (AType s p))
--
    (Alias x t) * u = alias x (t * u)
    t * (Alias x u) = alias x (t * u)

-- compare each subterm of the lhs to its expected form,
-- as defined by the annotated type of the function, such that
-- we obtain for each variable on the lhs a pattern of the form x\r,
-- with x an annotated variable and r a sum of contructor pattern,
-- expressing its expected shape as induced by the annotated type.
-- the corresponding variable in the rhs is then replaced by this pattern.
-- the obtained patterns are qsymb
replaceVariables :: Signature -> Rule -> [AType] -> [Rule]
replaceVariables sig (Rule (Appl f ls) rhs) d = foldl accuRule [] lterms
  where lterms = removePlusses (Appl f subLterms)
        subLterms = zipWith conjVar ls d
        conjVar t s = conjunction sig t (AVar NoName s)
        accuRule l lhs
          | any isBottom varMap = l -- if a variable has conflicting instances (PL: do we really need to test?)
          | otherwise           = (Rule lhs (typeCheck sig ((replaceVar varMap) rhs) s)):l
          where varMap = getVarMap lhs s -- c(ti) * x^-bot is reduced to c(ti) so we build the annotated sorts manually for variables of ti
                getVarMap t@(Alias x _) _ = M.singleton x t
                getVarMap (Appl g ts) _ = M.unionsWith (conjunction sig) (zipWith getVarMap ts (domain sig g))
                getVarMap (AVar x _) s = M.singleton x (AVar x (AType s Bottom))
                getVarMap (Compl (AVar x _) r) s = M.singleton x (Compl (AVar x (AType s Bottom)) r)
                replaceVar m (Appl f ts) = Appl f (map (replaceVar m) ts)
                replaceVar m (AVar x Unknown) = case M.lookup x m of
                  Just t  -> t
                  Nothing -> error ("variable " ++ show x ++ " unknown")
                s = range sig f

-- return the semantics equivalent of a term
buildEqui :: Signature -> Cache -> Term -> (Cache, Term)
buildEqui sig c0 t@(Appl f ts)
  | isFunc sig f = (c2, AVar (VarName (show t)) (AType (range sig f) p))
  | otherwise    = (c1, Appl f equis)
  where (c1, equis) = foldr buildSub (c0, []) ts
        buildSub t (cache, l) = (cache', t':l)
          where (cache', t') = buildEqui sig cache t
        (c2, p) = foldl accuCheck (c1, Bottom) (profile sig f)
        accuCheck (cache, p) (qs, q)
          | subFree   = (cache', plus p q)
          | otherwise = (cache', p)
          where (cache', subFree) = (foldr subCheck (\c -> (c, True)) (zip equis qs)) cache
        subCheck tp next cache
          | null fails = next cache'
          | otherwise = (cache', False)
          where (cache', fails) = checkPfree sig cache tp
buildEqui _ c t = (c, t)

-- type and put all annotations in qaddt form
normalizeSig :: Signature -> Signature
normalizeSig sig@(Signature ctors funs) = Signature ctors tFuns
  where tFuns = map normF funs
        normF (Function f d r pr) = (Function f d r (map normPr pr))
          where normPr (qs, p) = (map (reduce.typeP) (zip qs d), (reduce.typeP) (p, r))
                reduce Bottom = Bottom
                reduce v@(AVar _ _) = v
                reduce (Plus u1 u2) = Plus (reduce u1) (reduce u2)
                reduce (Compl u v) = complementR sig (reduce u) (reduce v)
                reduce (Appl g tl) = foldl buildTerm Bottom subterms
                  where subterms = foldl buildSet (S.singleton []) (reverse tl)
                        buildSet sl t = S.fold (S.union . (buildList t)) S.empty sl
                        buildList t l = S.map (:l) ((removePlusses.reduce) t)
                        buildTerm u l = plus u (Appl g l)
                typeP (p,s) = p # s
                  where
                    Bottom # _ = Bottom
                    (AVar x Unknown) # so      = AVar x (AType so Bottom)
                    v@(AVar x (AType _ _)) # _ = v
                    (Anti u)     # so = Compl (AVar NoName (AType so Bottom)) (u # so)
                    (Compl u v)  # so = Compl (u # so) (v # so)
                    (Plus u1 u2) # so = Plus (u1 # so) (u2 # so)
                    (Appl g tl)  # _  = Appl g (zipWith (#) tl (domain sig g))

-- check TRS : call checkRule for each rule and concatenate the results
-- return a map of failed rule with the terms that do not satisfy the expected pattern-free property
checkTRS :: Signature -> [Rule] -> M.Map Rule (Term,[Term])
checkTRS sig rules = snd (foldl accuCheck (emptyCache, M.empty) rules)
  where nSig = normalizeSig sig
        accuCheck (c, m) rule
          | null fails = (c', m)
          | otherwise  = (c', M.union m fails)
          where (c', fails) = checkRule nSig c rule

-- check rule : for each profile of the head function symbol of the left hand side,
-- alias the variables in the right hand side and build its semantics equivalent,
-- then check that the term obtained verifies the corresponding pattern-free property.
-- return a list of terms that do not satisfy the expected pattern-free properties
checkRule :: Signature -> Cache -> Rule -> (Cache, M.Map Rule (Term,[Term]))
checkRule sig c r@(Rule (Appl f _) _) = foldl accuCheck (c, M.empty) rules
  where accuCheck (cache, m) (Rule lhs rhs, p)
          | checkPfree2 sig (rhs, p) = (cache, m)
          | otherwise                = (cache, M.insert (Rule lhs rhs) (p, [rhs]) m)
--           | null fails = (cache2, m)
--           | otherwise  = (cache2, M.insert (Rule lhs equi) (p,fails) m)
--           where (cache1, equi) = buildEqui sig cache rhs
--                 (cache2, fails) = trace ("checking RULE " ++ show (Rule lhs equi)) (checkPfree sig cache1 (equi,p))
        rules = concatMap buildRule (map buildDomain (profile sig f))
        buildRule (_, Bottom) = []
        buildRule (ad, p) = zip (replaceVariables sig r ad) (repeat p)
        buildDomain (qs, p) = (zipWith AType d qs, p)
        d = domain sig f

-- check that a term is p-free
-- parameters: Signature, Pattern p (should be a sum of constructor patterns), Rhs term of a rule (should be a qsymb)
-- return a list of terms that do not satisfy the expected pattern-free property
checkPfree :: Signature -> Cache -> (Term, Term) -> (Cache, [Term])
checkPfree _ c (_, Bottom) = (c, [])
checkPfree sig c (t, p) = accuCheck (c, []) t
  where accuCheck (c'@(Cache m), l) u@(Appl _ ts) = case M.lookup (u,p) m of
          Just res -> (c', res ++ l)
          Nothing | check sig p u -> (Cache (M.insert (u, p) lSub mSub), lSub ++ l)
                  | otherwise        -> (Cache (M.insert (u, p) (u:lSub) mSub), u:(lSub ++ l))
                  where (Cache mSub, lSub) = foldl accuCheck (c',[]) ts
        accuCheck (c'@(Cache m), l) u@(AVar _ s) = case M.lookup (u',p) m of
          Just res -> trace ("checked AVar " ++ show u) (c', res ++ l)
          Nothing | all (check sig p) reachables -> (Cache (M.insert (u', p) [] m), l)
                  | otherwise                    -> (Cache (M.insert (u', p) [u'] m), u':l)
                  where reachables = trace ("checking AVar " ++ show u) (getReachable sig s S.empty)
          where u' = AVar NoName s
        accuCheck (c'@(Cache m), l) u@(Compl (AVar _ s) r) = case M.lookup (u',p) m of
          Just res -> (c', res ++ l)
          Nothing | all (check sig p) reachables -> (Cache (M.insert (u', p) [] m), l)
                  | otherwise                    -> (Cache (M.insert (u', p) [u'] m), u':l)
                  where reachables = trace ("checking Compl " ++ show u) (getReachable sig s (removePlusses r))
          where u' = Compl (AVar NoName s) r

-- check that t X p reduces to Bottom
-- with t a qaddt term and p a sum of constructor patterns
check :: Signature -> Term -> Term -> Bool
check _ Bottom _ = True
check sig p t = trace ("checking if BOTTOM: " ++ show t ++ " X " ++ show p) (checkConj (conjunction sig t p))
  where checkConj Bottom = True
        checkConj t = all (checkVariables sig) (removePlusses t)
-- check sig t (Plus p1 p2) = (check sig t p1) && (check sig t p2)

-- check if a term has conflicting instances of a variable
-- if at least one variable has conflicting instances, returns true
-- else false
checkVariables :: Signature -> Term -> Bool
checkVariables sig t = trace ("checking Variables in " ++ show t) (any isBottom (checkVar t))
  where checkVar v@(AVar x@(VarName _) _) = M.singleton x v
        checkVar (AVar NoName _) = M.empty
        checkVar (Alias x t) = M.singleton x t
        checkVar t@(Compl (AVar x@(VarName _) _) _) = M.singleton x t
        checkVar (Compl (AVar NoName _) _) = M.empty
        checkVar (Appl f ts) = M.unionsWith (conjunction sig) (map checkVar ts)


data CheckMap = VarMap (M.Map VarName (Term, [Term]))
              | BotMap

checkGlue :: Signature -> (Term, [Term]) -> (Term, [Term]) -> (Term, [Term])
checkGlue _ (Bottom, _) (_, _) = (Bottom, [])
checkGlue _ (_, _) (Bottom, _) = (Bottom, [])
checkGlue sig (AVar _ _, q1) (t2, q2)
  | checkInstance sig t2 ql = (t2, ql)
  | otherwise               = (Bottom, [])
  where ql = q1 ++ q2
checkGlue sig (t1, q1) (AVar _ _, q2)
  | checkInstance sig t1 ql = (t1, ql)
  | otherwise               = (Bottom, [])
  where ql = q1 ++ q2
checkGlue sig (t1, q1) (t2, q2)
  | checkInstance sig txt ql = (txt, ql)
  | otherwise                = (Bottom, [])
  where txt = conjunction sig t1 t2
        ql = q1 ++ q2

checkInsert :: Signature -> VarName -> (Term, [Term]) -> CheckMap -> CheckMap
checkInsert _ _ _ BotMap = BotMap
-- checkInsert sig x tq@(t, q)  (VarMap vMap) = VarMap (M.alter glue x vMap)
--   where glue (Just tq') = Just (checkGlue sig tq tq')
--         glue Nothing | checkInstance sig t q = Just tq
--                      | otherwise             = Just (Bottom, [])
checkInsert sig x tq@(AVar _ _, q0) (VarMap vMap)
  | checkInstance sig t' q' = VarMap vMap'
  | otherwise               = BotMap
  where ((t', q'), vMap') = case M.insertLookupWithKey glue x tq vMap of
          (Nothing    , rMap) -> (tq, rMap)
          (Just (t, q), rMap) -> ((t, q++q0), rMap)
        glue _ _ (t, q) = (t, q++q0)
checkInsert sig x (t0, q0) (VarMap vMap)
  | checkInstance sig t' q' = VarMap (M.insert x (t', q') vMap)
  | otherwise               = BotMap
  where (t', q') = case M.lookup x vMap of
                     Nothing -> (t0, q0)
                     Just (t, q) -> (conjunction sig t0 t, q++q0)

getCheckMap :: Signature -> CheckMap -> Term -> CheckMap
getCheckMap _ BotMap _ = BotMap
getCheckMap _ cMap (AVar NoName _) = cMap
getCheckMap _ cMap (Compl (AVar NoName _) _) = cMap
getCheckMap sig cMap (Appl f ts) = foldl (getCheckMap sig) cMap ts
getCheckMap sig (VarMap vMap) t = VarMap m
  where m = case t of
              AVar x _             -> M.insertWith (checkGlue sig) x (t, []) vMap
              Alias x u            -> M.insertWith (checkGlue sig) x (u, []) vMap
              Compl (Alias x u) q  -> M.insertWith (checkGlue sig) x (u, collect q) vMap
              Compl v@(AVar x _) q -> M.insertWith (checkGlue sig) x (v, collect q) vMap

isBotMap :: CheckMap -> Bool
isBotMap BotMap = True
isBotMap (VarMap vMap) = any (isBottom.fst) vMap

-- check that a term is p-free
-- parameters: Signature, Pattern p (should be a sum of constructor patterns), Rhs term of a rule (should be a qsymb)
-- return a list of terms that do not satisfy the expected pattern-free property
checkPfree2 :: Signature -> (Term, Term) -> Bool
checkPfree2 _ (_, Bottom) = True
checkPfree2 sig (t0, p0) = trace ("checking " ++ show p0 ++ "-free: " ++ show t0) (recCheck t0 [p0] (VarMap M.empty) [])
  where convert fSet x@(AVar _ _)  = (fSet, x)
        convert fSet a@(Alias _ _) = (fSet, a)
        convert fSet u@(Compl _ _) = (fSet, u)
        convert fSet u@(Appl f us)
          | isFunc sig f = (S.insert u fSet, v)
          | otherwise    = (fSet', Appl f vs)
          where (fSet', vs) = foldr accuConvert (fSet, []) us
                v = AVar (VarName (show u)) (AType (range sig f) Bottom)
        accuConvert ti (mi, tl) = (mi', ti':tl)
          where (mi', ti') = convert mi ti
        recCheck _ _ BotMap _ = True
        recCheck v@(AVar x _) pl cMap fList = nextF fList (checkInsert sig x (v, pl) cMap)
        recCheck (Alias x t) pl cMap fList = nextF fList (checkInsert sig x (t, pl) cMap)
        recCheck t@(Appl f ts) pl cMap@(VarMap vMap) fList = all ((checkNextF (S.toList fSet)) . (getCheckMap sig cMap)) tmSet
          where (fSet, ts') = foldr accuConvert (S.fromList fList, []) ts
                tmSet = removePlusses (complementA sig (Appl f ts') (sumTerm cl))
                  where cl | isFunc sig f = map ((Appl f) . (zipWith buildVar d)) profiles
                           | otherwise    = zipWith (flip buildVar) pl (repeat s)
                           where s = range sig f
                                 d = domain sig f
                                 buildVar si qi = AVar NoName (AType si qi)
                                 profiles = selectProfiles sig f u pl'
                                 (u, pl') = case M.lookup (VarName (show t)) vMap of
                                   Just (v, ql) -> (v, pl++ql)
                                   Nothing -> (AVar NoName (AType s Bottom), pl)
        nextF _ BotMap = True
        nextF [] _ = False
        nextF (tf:fList) cMap = recCheck tf [] cMap fList
        checkNextF [] cMap = isBotMap cMap
        checkNextF (tf:fList) cMap
          | isBotMap cMap = True
          | otherwise     = recCheck tf [] cMap fList

selectProfiles :: Signature -> FunName -> Term -> [Term] -> [[Term]]
selectProfiles sig f t ql = map fst (fst (getCombinations part))
  where part = partition checkProfile (profile sig f)
        getCombinations (okl, []) =  (okl, [])
        getCombinations (okl, ((d,r):tail)) = (recokl, (d,r):reckol)
          where (recokl, reckol) = case getCombinations (okl, tail) of
                  (oktail, kotail) -> (oktail ++ okdist, kotail ++ kodist)
                    where (okdist, kodist) = partition checkProfile (map sumProfile kotail)
                sumProfile (d', r') = (zipWith plus d d', plus r r')
        checkProfile (_, r) = all checkRange (removePlusses (conjunction sig t (AVar NoName (AType s r))))
        checkRange u = not (checkInstance sig u ql)
        s = range sig f


-------------------------------- getReachable: --------------------------------

data Reach = Reach TypeName (S.Set Term)
  deriving (Eq, Ord)

-- Burn After Reading
--instance Show Reach where
--  show (Reach s r) | null r    = "x : " ++ show s ++ " \\ bot"
--                   | otherwise = "x : " ++ show s ++ " \\ (" ++ (concatMap show r) ++ ")"
--

data Cache = Cache (M.Map (Term, Term) [Term])

emptyCache = Cache M.empty

-- getReachable :: Cache -> Signature -> Term -> TypeName -> (Cache, S.Set Reach)
-- getReachable c@(Cache m1 m2) sig p s = case M.lookup (p, reach) m1 of
--   Just a  -> (c, a)
--   Nothing -> (Cache (M.insert (p, reach) res m1) m2, res)
--   where res = getReach c sig p reach S.empty
--         reach = Reach s S.empty
-- 
-- getReachableR :: Cache -> Signature -> Term -> TypeName -> S.Set Term -> (Cache, S.Set Reach)
-- getReachableR c@(Cache m1 m2) sig p s r = case M.lookup (p, reach) m1 of
--   Just a  -> (c, a)
--   Nothing -> (Cache (M.insert (p, reach) res m1) m2, res)
--   where res = getReach c sig p reach S.empty
--         reach = Reach s r

getReachable :: Signature -> AType -> S.Set Term -> S.Set Term
getReachable sig (AType s p) r = S.map buildComplement reaches
  where reaches = getReach sig s p r
        buildComplement (Reach s' p')
          | null p'   = (AVar NoName (AType s' p))
          | otherwise = Compl (AVar NoName (AType s' p)) (sumTerm p')

-- abandon hope all ye who enter here
getReach :: Signature -> TypeName -> Term -> S.Set Term -> S.Set Reach
getReach sig s0 p r0
  | any isVar r0 = S.empty --computeQc filters out variables, so we just need to do this for r0
  | otherwise    = computeReach s0 r0 S.empty
  where pSet = removePlusses p
        recCompute (si, qi) next dReach
          | null iReach = iReach -- not computing more reach when one qi has already failed
          | otherwise   = next iReach -- sequentially computing reaches to avoid performing unions
          where iReach = computeReach si qi dReach
        computeReach s r sReach
          | S.member (Reach s r) sReach = sReach
          | otherwise                   = fromMaybe S.empty (foldl accuReach Nothing (ctorsOfRange sig s))
          where r' | hasType sig p s = S.union r pSet
                   | otherwise       = r
                reach' = S.insert (Reach s r) sReach
                accuReach dReach c = foldl accuSubReach dReach (computeQc sig c r')
                  where d = domain sig c
                        accuSubReach rReach q
                          | null tReach = rReach -- ignores result when empty, ie not instantiable
                          | otherwise   = Just tReach
                          where tReach = (foldr recCompute id (zip d q)) (fromMaybe reach' rReach)

isInstantiable :: Signature -> TypeName -> Term -> S.Set Term -> Bool
isInstantiable sig s p r = not (null (getReachMin sig s p r))

-- stops when proof that the semantics is not empty
getReachMin :: Signature -> TypeName -> Term -> S.Set Term -> S.Set Reach
getReachMin sig s0 p r0
  | any isVar r0 = S.empty
  | otherwise    = computeReach s0 r0 S.empty
  where pSet = removePlusses p
        recCompute (si, qi) next rReach
          | null iReach = iReach
          | otherwise   = next iReach
          where iReach = computeReach si qi rReach
        computeReach s r sReach
          | S.member (Reach s r) sReach = sReach
          | otherwise                   = foldr accuReach S.empty (ctorsOfRange sig s)
          where r' | hasType sig p s = S.union r pSet
                   | otherwise       = r
                reach' = S.insert (Reach s r) sReach
                accuReach c dReach
                  | null qReach = dReach
                  | otherwise   = qReach
                  where qReach = foldr accuSubReach S.empty (computeQc sig c r')
                        d = domain sig c
                        accuSubReach q rReach
                          | null tReach = rReach
                          | otherwise   = tReach
                          where tReach = (foldr recCompute id (zip d q)) reach'

computeQc :: Signature -> FunName -> (S.Set Term) -> [[S.Set Term]]
computeQc sig c r = foldr getDist [replicate (length d) S.empty] r
  where getDist (Appl g ts) tQc
          | c == g    = concatMap accuDist tQc
          | otherwise = tQc
          where accuDist q = distribute q ts
                distribute [] [] = []
                distribute (qi:ql) (ti:tl)
                  | isVar ti  = tail -- filter out variables to avoid empty semantics
                  | otherwise = ((S.insert ti qi) : ql) : tail
                  where tail = map (qi:) (distribute ql tl)
        d = domain sig c

isVar :: Term -> Bool
isVar (AVar _ _)   = True
isVar (Plus t1 t2) = (isVar t1) || (isVar t2)
isVar _            = False



-- check if there exists an instance of a linear pattern that is not
-- p-free for all p in q0
checkInstance :: Signature -> Term -> [Term] -> Bool
checkInstance _ Bottom _ = False
checkInstance sig t0 q0
  | any isBottom q0 = False
  | otherwise       = computeInstance M.empty t0 q0
  where computeInstance _ _ [] = True
        computeInstance reach t q = case M.lookup t reach of
          Nothing -> any conjInstance powerQ
          Just q' | isSubsequenceOf q' q -> False
                  | otherwise            -> any conjInstance powerQ
          where powerQ = foldr powerConj [([], t)] q
                subReach = M.insert t q reach
                conjInstance (qSet, qConj) = any subInstance (removePlusses qConj)
                  where subInstance (Appl _ []) = null qDiff
                        subInstance (Appl _ ts) = any (all (uncurry (computeInstance subReach))) (computeQt ts qDiff)
                        subInstance (AVar _ s) = any subInstance (computePatterns s S.empty)
                        subInstance (Compl (AVar _ s) r) = any subInstance (computePatterns s (removePlusses r))
                        subInstance (Alias _ u) = subInstance u
                        qDiff = q \\ qSet
        powerConj q l = concatMap accuConj l
          where accuConj (ql, t)
                  | isBottom txq = [(ql, t)]
                  | otherwise    = (q:ql, txq):[(ql, t)]
                  where txq = conjunction sig t q
        computePatterns (AType s p) rSet = concatMap buildPatterns (ctorsOfRange sig s)
          where prSet = S.union rSet (removePlusses p)
                buildPatterns f =  mapMaybe buildCompl (computeQc sig f prSet)
                  where buildCompl qs
                          | any isBottom xqs = Nothing
                          | otherwise = Just (Appl f xqs)
                          where xqs = zipWith (complementR sig) xs (map sumTerm qs)
                        xs = map buildVar (domain sig f)
                        buildVar si = AVar NoName (AType si p)


computeQt :: [Term] -> [Term] -> [[(Term, [Term])]]
computeQt ts qs = foldr getDist [zip ts (repeat [])] qs
  where getDist q tQ = concatMap distribute tQ
          where distribute [] = []
                distribute ((t,xl):ql) = ((t, q:xl):ql):(map ((t,xl):) (distribute ql))















----------------------------- not used anymore --------------------------------
typeVariables :: Signature -> [Rule] -> [Rule]
typeVariables sig rules = map (inferVarType sig) rules

inferVarType :: Signature -> Rule -> Rule
inferVarType sig (Rule lhs rhs) = Rule lhs (replaceVar varMap rhs)
  where replaceVar m (Appl f ts) = Appl f (map (replaceVar m) ts)
        replaceVar m (AVar x Unknown) = m M.! x
        varMap = getVarMap M.empty lhs
          where getVarMap m (Appl f ts) = foldl getVarMap (updateMap ts f m) ts
                getVarMap m _ = m
                updateMap ts f m = foldl mapVariables m (zip ts (domain sig f))
                  where mapVariables m ((AVar x _), s) = M.insert x (AVar x (AType s Bottom)) m
                        mapVariables m _ = m
