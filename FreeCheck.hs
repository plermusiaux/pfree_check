{-# LANGUAGE OverloadedStrings #-}

module FreeCheck (checkTRS) where

import Debug.Trace
import Data.List ( tails, inits )
import Data.Maybe
import qualified Data.Map as M
import qualified Data.Set as S
import Datatypes
import Signature

--------------------------------- From Algo: ----------------------------------

isBottom :: Term -> Bool
isBottom Bottom = True
isBottom t = False

-- interleave abc ABC = Abc, aBc, abC
interleave :: [a] -> [a] -> [[a]]
interleave [] [] = []
interleave xs ys = zipWith3 glue (inits xs) ys (tails (tail xs))
  where glue xs x ys = xs ++ x : ys

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
        buildSet sl t = S.fold (S.union . (buildList t)) S.empty sl
        buildList t l = S.map (flip (:) l) (removePlusses t)
removePlusses v@(AVar _ _) = S.singleton v
removePlusses Bottom = S.empty
removePlusses a@(Alias x p) = S.singleton a
--removePlusses (Alias x p) = S.map (Alias x) (removePlusses p)

complement :: Signature -> Term -> Term -> Term
complement sig p1 p2 = p1 \\ p2
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
    (Compl v t) \\ u = v \\ (plus t u)                                    --P5
    v@(AVar x sp@(AType s p)) \\ t
        | isBottom p               = sumTerm [pattern c \\ t | c <- cs]
        | isInstantiable sig p s r = Compl v t --Alias x (Compl (AVar NoName sp) t)
        | otherwise                = Bottom                               --P6
        where cs = ctorsOfRange sig s
              pattern c = Appl c (map buildVar (domain sig c))
              buildVar si = AVar NoName (AType si p)
              r = removePlusses t
    Alias x p1 \\ p2 = alias x (p1 \\ p2)
--    p1 \\ Alias x p2 = p1 \\ p2

-------------------------------------------------------------------------------

conjunction :: Signature -> Term -> Term -> Term
conjunction sig p1 p2 = p1 * p2
  where 
    Bottom * u = Bottom                                                   --E2
    u * Bottom = Bottom                                                   --E3
    (Plus u1 u2) * u = plus (u1 * u) (u2 * u)                             --S2
    u * (Plus u1 u2) = plus (u * u1) (u * u2)                             --S3
    v@(AVar x aType) * (AVar y (AType s2 p2)) = case aType of
                                      -- Generalization of T1/T2 for variables
        Unknown -> Alias x (AVar x (AType s2 p2))
        AType s1 p1
          | s1 /= s2     -> Bottom
          | p1 == p2     -> v
          | p1 == Bottom -> AVar x (AType s2 p2)
          | p2 == Bottom -> v
--          | otherwise    -> (AVar x (AType s1 (Plus p1 p2)))
-- This should never happen, check isInstanciable sig (plus p1 p2) s1, if it does...
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
        | s == range sig f = complement sig (alias x (Appl f zXts)) p     --P1
        | otherwise        = Bottom
        where zXts = zipWith conjVar (domain sig f) ts
              conjVar si t = (AVar NoName (AType si p)) * t
    (Appl f ts) * (AVar x (AType s p))
        | s == range sig f = complement sig (Appl f tXzs) p
        | otherwise        = Bottom
        where tXzs = zipWith conjVar ts (domain sig f)
              conjVar t si = t * (AVar NoName (AType si p))
    v1 * (Compl v2 t) = complement sig (v1 * v2) t                        --P2-3
    (Compl v t) * u = complement sig (v * u) t                            --P4
--    (Var x) * u = Alias x u
--    (Appl f ts) * (AVar _ (AType _ p)) = complement sig (Appl f tsXz) p
--        where tsXz = zipWith conjVar ts (domain sig f)
--              conjVar t s = t * (AVar (VarName (show t)) (AType s p))
--
    (Alias x t) * u = alias x (t * u)

-- compare each subterm of the lhs to its expected form,
-- as defined by the annotated type of the function, such that
-- we obtain for each variable on the lhs a pattern of the form x\r,
-- with x an annotated variable and r a sum of contructor pattern,
-- expressing its expected shape as induced by the annotated type.
-- the corresponding variable in the rhs is then replaced by this pattern.
-- the obtained patterns are qaddt (without Plus)
replaceVariables :: Signature -> Rule -> [AType] -> [Rule]
replaceVariables sig (Rule (Appl f ls) rhs) d = foldl accuRule [] lterms
  where lterms = removePlusses (Appl f subLterms)
        subLterms = zipWith conjVar ls d
        conjVar t s = conjunction sig t (AVar NoName s)
        accuRule l lhs
          | any isBottom varMap = l -- if a variable has conflicting instances (PL: do we really need to test?)
          | otherwise           = (Rule lhs (typeCheck sig ((replaceVar varMap) rhs) s)):l
          where varMap = getVarMap lhs s -- c(ti) * x^-bot is reduced to c(ti) so we build the annotated sorts manually for variables of ti
                getVarMap (Alias x t) _ = M.singleton x t
                getVarMap (Appl g ts) _ = M.unionsWith (conjunction sig) (zipWith getVarMap ts (domain sig g))
                getVarMap (AVar x _) s = M.singleton x (AVar x (AType s Bottom))
                replaceVar m (Appl f ts) = Appl f (map (replaceVar m) ts)
                replaceVar m (AVar x Unknown)
                  | M.member x m = m M.! x
                  | otherwise    = error ("variable " ++ show x ++ " unknown")
                s = range sig f

-- return the semantics equivalent of a term
buildEqui :: Signature -> Cache -> Term -> (Cache, Term)
buildEqui sig c t@(Appl f ts)
  | isFunc sig f = (c2, AVar (VarName (show t)) (AType (range sig f) p))
  | otherwise    = (c1, Appl f equis)
  where (c1, equis) = foldr buildSub (c, []) ts
        buildSub t (cache, l) = (cache', t':l)
          where (cache', t') = buildEqui sig cache t
        (c2, p) = foldl accuCheck (c1, Bottom) (profile sig f)
        accuCheck (cache, p) (qs, q)
          | subFree   = (cache', plus p q)
          | otherwise = (cache', p)
          where (cache', subFree) = foldl subCheck (cache, True) (zip equis qs)
        subCheck (cache, False) _ = (cache, False)
        subCheck (cache, True) (_, Bottom) = (cache, True)
        subCheck (cache, True) tp = (cache', null fails)
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
                reduce (Compl u v) = complement sig (reduce u) (reduce v)
                reduce (Appl g tl) = foldl buildTerm Bottom subterms
                  where subterms = foldl buildSet (S.singleton []) (reverse tl)
                        buildSet sl t = S.fold (S.union . (buildList t)) S.empty sl
                        buildList t l = S.map (flip (:) l) ((removePlusses.reduce) t)
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
-- then check that the term obtained verify the corresponding pattern-free property.
-- return a list of terms that do not satisfy the expected pattern-free properties
checkRule :: Signature -> Cache -> Rule -> (Cache, M.Map Rule (Term,[Term]))
checkRule sig c r@(Rule (Appl f _) _) = foldl accuCheck (c, M.empty) rules
  where accuCheck (cache, m) (Rule lhs rhs, p)
          | null fails = (cache2, m)
          | otherwise  = (cache2, M.insert (Rule lhs equi) (p,fails) m)
          where (cache1, equi) = buildEqui sig cache rhs
                (cache2, fails) = trace ("checking RULE " ++ show (Rule lhs equi)) (checkPfree sig cache1 (equi,p))
        rules = concatMap buildRule (map buildDomain (profile sig f))
        buildRule (_, Bottom) = []
        buildRule (ad, p) = zip (replaceVariables sig r ad) (repeat p)
        buildDomain (qs, p) = (zipWith AType d qs, p)
        d = domain sig f

-- check that a term is p-free
-- parameters: Signature, Pattern p (should be a sum of constructor patterns), Rhs term of a rule (should be a qaddt without Plus)
-- return a list of terms that do not satisfy the expected pattern-free property
checkPfree :: Signature -> Cache -> (Term, Term) -> (Cache, [Term])
checkPfree _ c (_, Bottom) = (c, [])
checkPfree sig c (t, p) = accuCheck (c, []) t
  where accuCheck (c'@(Cache m), l) u@(Appl _ ts) = case M.lookup (u,p) m of
          Just res -> (c', res ++ l)
          Nothing | check sig p u -> (Cache (M.insert (u, p) lSub mSub), lSub ++ l)
                  | otherwise        -> (Cache (M.insert (u, p) (u:lSub) mSub), u:(lSub ++ l))
                  where (Cache mSub, lSub) = foldl accuCheck (c',[]) ts
        accuCheck (c'@(Cache m), l) u@(AVar _ (AType s q)) = case M.lookup (u',p) m of
          Just res -> trace ("checked AVar " ++ show u) (c', res ++ l)
          Nothing | all (check sig p) reachables -> (Cache (M.insert (u', p) [] m), l)
                  | otherwise                    -> (Cache (M.insert (u', p) [u'] m), u':l)
                  where reaches = trace ("checking AVar " ++ show u) getReachable sig q s
                        reachables = S.map buildComplement reaches
                        buildComplement (Reach s' p')
                          | null p'   = (AVar "_" (AType s' q))
                          | otherwise = Compl (AVar "_" (AType s' q)) (sumTerm p')
          where u' = AVar NoName (AType s q)
        accuCheck (c'@(Cache m), l) u@(Compl (AVar _ (AType s q)) r) = case M.lookup (u',p) m of
          Just res -> trace ("checked Compl " ++ show u) (c', res ++ l)
          Nothing | all (check sig p) reachables -> (Cache (M.insert (u', p) [] m), l)
                  | otherwise                    -> (Cache (M.insert (u', p) [u'] m), u':l)
                  where reaches = trace ("checking Compl " ++ show u) getReachableR sig q s (removePlusses r)
                        reachables = S.map buildComplement reaches
                        buildComplement (Reach s' p')
                          | null p'   = (AVar "_" (AType s' q))
                          | otherwise = Compl (AVar "_" (AType s' q)) (sumTerm p')
          where u' = Compl (AVar NoName (AType s q)) r

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
        checkVar (Alias x t) = M.singleton x t
        checkVar t@(Compl (AVar x _) _) = M.singleton x t
        checkVar (Appl f ts) = M.unionsWith (conjunction sig) (map checkVar ts)

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

getReachable :: Signature -> Term -> TypeName -> S.Set Reach
getReachable sig p s = getReach sig p (Reach s S.empty) S.empty

getReachableR :: Signature -> Term -> TypeName -> S.Set Term -> S.Set Reach
getReachableR sig p s r = getReach sig p (Reach s r) S.empty

isInstantiable :: Signature -> Term -> TypeName -> S.Set Term -> Bool
isInstantiable sig p s r = not (null (getReachMin sig p (Reach s r) S.empty))

-- abandon hope all ye who enter here
getReach :: Signature -> Term -> Reach -> S.Set Reach -> S.Set Reach
getReach sig p (Reach s0 r0) reach
  | any isVar r0 = S.empty --computeQc filters out variables, so we just need to do this for r0
  | otherwise    = computeReach s0 r0 reach
  where pSet = removePlusses p
        computeReach s r sReach
          | S.member (Reach s r) sReach = sReach
          | otherwise                   = fromMaybe S.empty (foldl accuReach Nothing (ctorsOfRange sig s))
          where r' | hasType sig p s = S.union r pSet
                   | otherwise       = r
                reach' = S.insert (Reach s r) sReach
                accuReach cReach c = foldl accuSubReach cReach (computeQc sig c r')
                  where d = domain sig c
                        accuSubReach qReach q
                          | null tReach = qReach -- ignores result when empty, ie not instantiable
                          | otherwise   = Just tReach
                          where tReach = foldl compute (fromMaybe reach' qReach) cRs
                                cRs = zipWith computeReach d q
                                compute iReach cR
                                  | null iReach = iReach -- not computing more reach when one qi has already failed
                                  | otherwise   = cR iReach -- sequentially computing reaches to avoid performing unions

-- stops when proof that the semantics is not empty
getReachMin :: Signature -> Term -> Reach -> S.Set Reach -> S.Set Reach
getReachMin sig p (Reach s0 r0) reach
  | any isVar r0 = S.empty
  | otherwise    = computeReach s0 r0 reach
  where pSet = removePlusses p
        computeReach s r sReach
          | S.member (Reach s r) sReach = sReach
          | otherwise                   = fromMaybe S.empty (foldl accuReach Nothing (ctorsOfRange sig s))
          where r' | hasType sig p s = S.union r pSet
                   | otherwise       = r
                reach' = S.insert (Reach s r) sReach
                accuReach m@(Just _) _ = m
                accuReach Nothing    c = foldl accuSubReach Nothing (computeQc sig c r')
                  where d = domain sig c
                        accuSubReach m@(Just _) _ = m
                        accuSubReach Nothing    q
                          | null tReach = Nothing
                          | otherwise   = Just tReach
                          where tReach = foldl compute reach' cRs
                                cRs = zipWith computeReach d q
                                compute iReach cR
                                  | null iReach = iReach
                                  | otherwise   = cR iReach

computeQc :: Signature -> FunName -> (S.Set Term) -> [[S.Set Term]]
computeQc sig c r = foldl getDist [replicate (length d) S.empty] r
  where getDist tQc (Appl g ts)
          | c == g    = foldl accuDist [] tQc
          | otherwise = tQc
          where accuDist sQc q = (mapMaybe (distribute q) (zip [0..] ts)) ++ sQc
                distribute q (i, t)
                  | isVar t   = Nothing -- filter out variables to avoid empty semantics
                  | otherwise = Just (pre ++ (S.insert t qi) : tail)
                  where (pre, qi : tail) = splitAt i q
        d = domain sig c

isVar :: Term -> Bool
isVar (AVar _ _)   = True
isVar (Plus t1 t2) = (isVar t1) || (isVar t2)
isVar _            = False




















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
