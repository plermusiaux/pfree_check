{-# LANGUAGE OverloadedStrings #-}

module FreeCheck (checkTRS) where

import Debug.Trace
import Data.List ( tails, inits )
import qualified Data.Vector as V
import qualified Data.Set as S
import qualified Data.Map as M
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

plus :: Term -> Term -> Term
plus Bottom u = u                                                         --A1
plus t Bottom = t                                                         --A2
plus t u = Plus t u

sumTerm :: [Term] -> Term
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
removePlusses v@(Var _) = S.singleton v
removePlusses v@(AVar _ _) = S.singleton v
removePlusses Bottom = S.empty
removePlusses (Alias x p) = S.map (Alias x) (removePlusses p)

complement :: Signature -> Term -> Term -> Term
complement sig p1 p2 = p1 \\ p2
  where
    alias x Bottom = Bottom
    alias x t = Alias x t

    u \\ (Var _) = Bottom                                                 --M1
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
    (Compl v t) \\ u = complement sig v (plus t u)                        --P5
    v@(AVar x (AType s p)) \\ t
        | null (getReach sig p (Reach s r) S.empty) = Bottom              --P6
        | otherwise                                = Compl v t
        where r = removePlusses t
    Alias x p1 \\ p2 = alias x (p1 \\ p2)
    p1 \\ Alias x p2 = p1 \\ p2

-------------------------------------------------------------------------------

conjunction :: Signature -> Term -> Term -> Term
conjunction sig p1 p2 = p1 * p2
  where 
    Bottom * u = Bottom                                                   --E2
    u * Bottom = Bottom                                                   --E3
    (Plus u1 u2) * u = plus (u1 * u) (u2 * u)                             --S2
    u * (Plus u1 u2) = plus (u * u1) (u * u2)                             --S3
    u * (Var _) = u                                                       --T1
    (AVar _ (AType s Bottom)) * u                                                 
        | hasType sig u s = u                                             --T2
        | otherwise       = Bottom
    Appl f ps * Appl g qs
        | f == g = appl f (zipWith (conjunction sig) ps qs)               --T3
        | otherwise = Bottom                                              --T4
    (AVar _ (AType s p)) * q@(Appl f ps)
        | s == range sig f = (sumTerm (map pattern fs)) * (complement sig q p) --P1
        | otherwise        = Bottom
        where fs = ctorsOfRange sig s
              pattern a = Appl a (map buildVar (domain sig a))
              buildVar si = AVar "_" (AType si p)
    v1 * (Compl v2 t) = complement sig (conjunction sig v1 v2) t               --P2-3
    (Compl v t) * u = complement sig (conjunction sig v u) t                   --P4



typeVariables :: Signature -> [Rule] -> [Rule]
typeVariables sig rules = map (inferVarType sig) rules

inferVarType :: Signature -> Rule -> Rule
inferVarType sig (Rule lhs rhs) = Rule lhs (replaceVar varMap rhs)
  where replaceVar m t@(Appl f ts) = Appl f (map (replaceVar m) ts)
        replaceVar m (Var x) = m M.! x
        varMap = getVarMap M.empty lhs
          where getVarMap m (Appl f ts) = foldl getVarMap (updateMap ts f m) ts
                getVarMap m _ = m
                updateMap ts f m = foldl mapVariables m (zip ts (domain sig f))
                  where mapVariables m ((Var x), s) = M.insert x (AVar x (AType s Bottom)) m
                        mapVariables m _ = m

buildEqui :: Signature -> Term -> Term
buildEqui sig t@(Appl f ts)
  | isFunc sig f = AVar (VarName (show t)) (aRange sig f)
  | otherwise    = Appl f (map (buildEqui sig) ts)
buildEqui sig t = t
  
checkTRS :: Signature -> [Rule] -> M.Map Rule [Term]
checkTRS sig rules = foldl accuCheck M.empty (typeVariables sig rules)
  where accuCheck m rule
          | null fails = m
          | otherwise  = M.insert rule fails m
          where fails = checkRule sig rule

checkRule :: Signature -> Rule -> [Term]
checkRule sig (Rule (Appl f ts) rhs)
  | (p == Bottom) = []
  | otherwise     = (checkComposition sig rhs) ++ (checkPfree sig p (buildEqui sig rhs))
  where p = pfree sig f

checkComposition :: Signature -> Term -> [Term]
checkComposition sig (Appl f ts)
  | isFunc sig f = concatMap check (zip ts (aDomain sig f)) ++ subCheck
  | otherwise    = subCheck
  where check (t, (AType _ Bottom)) = []
        check (t, (AType _ p)) = checkPfree sig p (buildEqui sig t)
        subCheck = concatMap (checkComposition sig) ts
checkComposition sig (AVar _ _) = []

checkPfree :: Signature -> Term -> Term -> [Term]
checkPfree sig p t@(Appl f ts)
  | (isBottom (conjunction sig t p)) = trace ("checking term " ++ show t) subFails
  | otherwise                        = trace ("checking term " ++ show t) (t:subFails)
  where subFails = concatMap (checkPfree sig p) ts
checkPfree sig p t@(AVar _ (AType s q)) = trace ("checking AVar " ++ show t) (S.toList (S.filter check reachables))
  where reachables = S.map buildComplement (getReachable sig q s)
        buildComplement (Reach s' p')
          | null p'   = (AVar "_" (AType s' q))
          | otherwise = Compl (AVar "_" (AType s' q)) (sumTerm (S.toList p'))
        check u = trace ("checking term " ++ show u) (not (isBottom (conjunction sig u p)))

-------------------------------- getReachable: --------------------------------

data Reach = Reach TypeName (S.Set Term)
  deriving (Eq, Ord)

-- Burn After Reading
--instance Show Reach where
--  show (Reach s r) | null r    = "x : " ++ show s ++ " \\ bot"
--                   | otherwise = "x : " ++ show s ++ " \\ (" ++ (concatMap show r) ++ ")"
--
getReachable :: Signature -> Term -> TypeName -> S.Set Reach
getReachable sig p s = getReach sig p (Reach s S.empty) S.empty

-- abandon hope all ye who enter here
getReach :: Signature -> Term -> Reach -> S.Set Reach -> S.Set Reach
getReach sig p (Reach s r) reach
  | (any isVar r')                = S.empty
  | (S.member (Reach s r') reach) = reach
  | otherwise                     = reachable (foldl accuReach (False, reach') (ctorsOfRange sig s))
  where r' | hasType sig p s = S.insert p r
           | otherwise       = r
        isVar (Var _) = True
        isVar _       = False
        reach' = S.insert (Reach s r') reach
        reachable (True, res) = res
        reachable (False, _ ) = S.empty
        accuReach (reachable, current) c
          | implementable = (True, cReach)
          | otherwise     = (reachable, current)
          where (implementable, cReach) =  foldl accuSubReach (False, current) qc
                -- compute Qc
                qc = foldl getDist [V.replicate (length d) S.empty] r'
                getDist tQc (Appl g ts)
                  | c == g    = foldl accuDist [] tQc
                  | otherwise = tQc
                  where accuDist sQc q = V.toList (V.imap (distribute q) (V.fromList ts)) ++ sQc
                        distribute q i t = V.accum (flip S.insert) q [(i,t)]
                -- recursive calls on q in Qc
                accuSubReach (qImpl, qReach) q = concatReaches (foldl computeReaches (True, [qReach]) sq)
                  where sq = zipWith Reach d (V.toList q)
                        -- optimized: no call when one of the qi as failed
                        computeReaches (instantiated, lReach) qi
                          | instantiated && (not (null subReach)) = (True, subReach:lReach)
                          | otherwise                             = (False, [])
                          where subReach = getReach sig p qi qReach
                        -- optimized: only compute union when instantiable
                        concatReaches (instantiated, lReach)
                          | instantiated = (True, S.unions lReach)
                          | otherwise    = (qImpl, qReach)
                d = domain sig c
