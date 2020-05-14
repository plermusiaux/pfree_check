{-# LANGUAGE OverloadedStrings, DeriveGeneric, DeriveAnyClass #-}

module FreeCheck (checkTRS, getReachable) where

import Data.List ( tails, inits )
import qualified Data.Vector as V
import qualified Data.Set as S
import qualified Data.Map as M
import Datatypes
import Signature

import GHC.Generics (Generic)
import Control.DeepSeq

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
removePlusses v@(AVar _ _) = S.singleton v
removePlusses Bottom = S.empty
removePlusses a@(Alias x p) = S.singleton a
--removePlusses (Alias x p) = S.map (Alias x) (removePlusses p)

complement :: Signature -> Term -> Term -> Term
complement sig p1 p2 = p1 \\ p2
  where
    alias x Bottom = Bottom
    alias x t = Alias x t

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
    v@(AVar x (AType s p)) \\ t
        | null (getReachableR sig p s r) = Bottom                         --P6
        | otherwise                      = Compl v t
        where r = removePlusses t
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
    (AVar y s) * (AVar x Unknown) = Alias x (AVar x s)    -- HC: used in replaceVariables
    u * (AVar _ (AType s Bottom)) = u                                     --T1
    (AVar _ (AType s Bottom)) * u
        | hasType sig u s = u                                             --T2
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
    (AVar _ (AType s p)) * (Appl f ts)
        | s == range sig f = complement sig (Appl f zXts) p               --P1
        | otherwise        = Bottom
        where zXts = zipWith conjVar ts (domain sig f)
              conjVar t s = (AVar (VarName (show t)) (AType s p)) * t
    v1 * (Compl v2 t) = complement sig (v1 * v2) t                        --P2-3
    (Compl v t) * u = complement sig (v * u) t                            --P4
--    (Var x) * u = Alias x u
--    (Appl f ts) * (AVar _ (AType _ p)) = complement sig (Appl f tsXz) p
--        where tsXz = zipWith conjVar ts (domain sig f)
--              conjVar t s = t * (AVar (VarName (show t)) (AType s p))


aliasing :: Signature -> [Rule] -> [Rule]
aliasing sig rules = concatMap (replaceVariables sig) rules

-- compare each subterm of the lhs to its expected form,
-- as defined by the annotated type of the function, such that
-- we obtain for each variable on the lhs a pattern of the form x\r,
-- with x an annotated variable and r a sum of contructor pattern,
-- expressing its expected shape as induced by the annotated type.
-- the corresponding variable in the rhs is then replaced by this pattern.
-- the obtained patterns are qaddt (without Plus)
replaceVariables :: Signature -> Rule -> [Rule]
replaceVariables sig (Rule (Appl f ls) rhs) = map buildRule lterms
  where lterms = S.toList (removePlusses (Appl f subLterms))
        subLterms = zipWith conjVar ls (aDomain sig f)
        conjVar t s = conjunction sig (AVar (VarName (show t)) s) t
        buildRule l = Rule l (typeCheck sig ((replaceVar varMap) rhs) s)
          where varMap = getVarMap l s
                getVarMap (Alias x t) _ = M.singleton x t
                getVarMap (Appl g ts) _ = M.unions (zipWith getVarMap ts (domain sig g))
                getVarMap (AVar x _) s = M.singleton x (AVar x (AType s Bottom))
                replaceVar m (Appl f ts) = Appl f (map (replaceVar m) ts)
                replaceVar m (AVar x Unknown)
                  | M.member x m = m M.! x
                  | otherwise    = error ("variable " ++ show x ++ " unknown")
                s = range sig f

-- return the semantics equivalent of a term
buildEqui :: Signature -> Term -> Term
buildEqui sig t@(Appl f ts)
  | isFunc sig f = AVar (VarName (show t)) (aRange sig f)
  | otherwise    = Appl f (map (buildEqui sig) ts)
buildEqui sig t = t

-- check that t X p reduces to Bottom
-- with t a qaddt term and p a sum of constructor patterns
check :: Signature -> Term -> Term -> Bool
check sig t Bottom = True
check sig t p@(Appl f _)
  | hasType sig t (range sig f) = isBottom (conjunction sig t p)
  | otherwise                   = True
check sig t (Plus p1 p2) = (check sig t p1) && (check sig t p2)

-- check TRS : alias the variables in the right term of each rule and call checkRule
-- return a map of failed rule with the terms that do not satisfy the expected pattern-free property
checkTRS :: Signature -> [Rule] -> M.Map Rule [Term]
checkTRS sig rules = foldl accuCheck M.empty (aliasing tSig rules)
  where tSig = typePfreeSig sig
        accuCheck m rule
          | null fails = m
          | otherwise  = M.insert rule fails m
          where fails = checkRule tSig rule

-- check rule : check that the right term satisfies the expected pattern-free properties
-- return a list of terms that do not satisfy the expected pattern-free property
checkRule :: Signature -> Rule -> [Term]
checkRule sig r@(Rule (Appl f ts) rhs)
  | (p == Bottom) = checkCompliance sig rhs
  | otherwise     = (checkCompliance sig rhs) ++ (checkPfree sig p (buildEqui sig rhs))
  where p = pfree sig f

-- check in a term that all arguments of a function call satisfy the expected pattern-free property
-- parameters : Signature, Rhs term of a rule (should be a qaddt without Plus)
-- return a list of terms that do not satisfy the expected pattern-free property
checkCompliance :: Signature -> Term -> [Term]
checkCompliance sig (Appl f ts)
  | isFunc sig f = concatMap checkAType (zip ts (aDomain sig f)) ++ subCheck
  | otherwise    = subCheck
  where checkAType (t, AType _ p) = checkPfree sig p (buildEqui sig t)
        subCheck = concatMap (checkCompliance sig) ts
checkCompliance sig (Compl t u) = checkCompliance sig t   -- HC: not u instead of t?
-- PL: no in practice there is a Compl in the rhs of a rule only when a variable has been "aliased" by this Compl (so this is theoritically useless)
-- checkCompliance sig (Compl (AVar _ _) _) = [] -- would be a more appropriate definition (similarily as in checkPfree btw...)
-- in doubt, if there is a function call, it should be in the left side of the Compl, so we still check the left side just in case...
checkCompliance sig (AVar _ _) = []

-- check that a term is p-free
-- parameters: Signature, Pattern p (should be a sum of constructor patterns), Rhs term of a rule (should be a qaddt without Plus)
-- return a list of terms that do not satisfy the expected pattern-free property
checkPfree :: Signature -> Term -> Term -> [Term]
checkPfree sig Bottom t = []
checkPfree sig p t@(Appl f ts)
  | check sig t p = subFails
  | otherwise     = t:subFails
  where subFails = concatMap (checkPfree sig p) ts
checkPfree sig p t@(AVar _ (AType s q)) = S.toList (S.filter ncheck reachables)
  where reachables = S.map buildComplement (getReachable sig q s)
        buildComplement (Reach s' p')
          | null p'   = (AVar "_" (AType s' q))
          | otherwise = Compl (AVar "_" (AType s' q)) (sumTerm (S.toList p'))
        ncheck t = not (check sig t p)
checkPfree sig p t@(Compl (AVar _ (AType s q)) r) = S.toList (S.filter ncheck reachables)
  where reachables = S.map buildComplement (getReachableR sig q s (removePlusses r))
        buildComplement (Reach s' p')
          | null p'   = (AVar "_" (AType s' q))
          | otherwise = Compl (AVar "_" (AType s' q)) (sumTerm (S.toList p'))
        ncheck t = not (check sig t p)

-------------------------------- getReachable: --------------------------------

data Reach = Reach TypeName (S.Set Term)
  deriving (Eq, Ord, Generic, NFData)

-- Burn After Reading
--instance Show Reach where
--  show (Reach s r) | null r    = "x : " ++ show s ++ " \\ bot"
--                   | otherwise = "x : " ++ show s ++ " \\ (" ++ (concatMap show r) ++ ")"
--
getReachable :: Signature -> Term -> TypeName -> S.Set Reach
getReachable sig p s = getReach sig p (Reach s S.empty) S.empty

getReachableR :: Signature -> Term -> TypeName -> S.Set Term -> S.Set Reach
getReachableR sig p s r = getReach sig p (Reach s r) S.empty

-- abandon hope all ye who enter here
getReach :: Signature -> Term -> Reach -> S.Set Reach -> S.Set Reach
getReach sig p (Reach s r) reach
  | (any isVar r')                = S.empty
  | (S.member (Reach s r') reach) = reach
  | otherwise                     = reachable (foldl accuReach (False, reach') (ctorsOfRange sig s))
  where r' | hasType sig p s = S.union r (removePlusses p) --S.insert p r
           | otherwise       = r
        isVar (AVar _ _) = True
        isVar _          = False
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
