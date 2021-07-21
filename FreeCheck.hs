{-# LANGUAGE OverloadedStrings #-}

module FreeCheck (checkTRS) where

import Debug.Trace

import Data.Maybe
import qualified Data.Map as M
import qualified Data.Set as S

import AlgoUtils ( isBottom, plus, removePlusses )
import Datatypes
import FreeCheckNL ( checkPfreeNL, CheckMap(..), getCheckMap, isBotMap )
import Signature
import Reach ( getReachable )
import ReducePattern ( conjunction, normalizeSig, replaceVariables )

------------------------------------------------------------------------------

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

------------------------------------------------------------------------------

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
          | isFLinear sig rhs = if null fails
                                then (cache2, m)
                                else (cache2, M.insert (Rule lhs equi) (p,fails) m)
          | nlcheck           = (cache, m)
          | otherwise         = (cache, M.insert (Rule lhs rhs) (p, [rhs]) m)
          where (cache1, equi) = buildEqui sig cache rhs
                (cache2, fails) = trace ("checking RULE " ++ show (Rule lhs equi)) (checkPfree sig cache1 (equi,p))
                nlcheck = trace ("checking NL RULE " ++ show (Rule lhs rhs)) (checkPfreeNL sig (rhs, p))
        rules = concatMap buildRule (map buildDomain (profile sig f))
        buildRule (_, Bottom) = []
        buildRule (ad, p) = zip (replaceVariables sig r ad) (repeat p)
        buildDomain (qs, p) = (zipWith AType d qs, p)
        d = domain sig f

-- check that a Term has no shared variable in different parameters of
-- a function symbol
isFLinear :: Signature -> Term -> Bool
isFLinear sig t0 = isJust (getOKVar t0)
  where getOKVar (Alias x _) = Just (S.singleton x)
        getOKVar (AVar x _) = Just (S.singleton x)
        getOKVar (Compl (AVar x _) _) = Just (S.singleton x)
        getOKVar (Appl f ts)
          | (isFunc sig f) && not (checkInter vts) = Nothing
          | otherwise                              = uVar
          where vts = map getOKVar ts
                uVar = foldr checkUnion (Just S.empty) vts
                checkUnion Nothing _ = Nothing
                checkUnion _ Nothing = Nothing
                checkUnion (Just a) (Just b) = Just (S.union a b)
                checkInter [] = True
                checkInter (h:tail) = case h of
                  Nothing  -> False
                  Just vti -> (checkInter tail) && (all check (catMaybes tail))
                                where check vtj = null (S.intersection vti vtj)

-- check that a term is p-free
-- parameters: Signature, Pattern p (should be a sum of constructor patterns), Rhs term of a rule (should be a qsymb)
-- return a list of terms that do not satisfy the expected pattern-free property
checkPfree :: Signature -> Cache -> (Term, Term) -> (Cache, [Term])
checkPfree _ c0 (_, Bottom) = (c0, [])
checkPfree sig c0 (t, p) = accuCheck (c0, []) t
  where accuCheck (c@(Cache m), l) u@(Appl _ ts) = case M.lookup (u,p) m of
          Just res -> (c, res ++ l)
          Nothing | check sig p u -> (Cache (M.insert (u, p) lSub mSub), lSub ++ l)
                  | otherwise        -> (Cache (M.insert (u, p) (u:lSub) mSub), u:(lSub ++ l))
                  where (Cache mSub, lSub) = foldl accuCheck (c,[]) ts
        accuCheck (c@(Cache m), l) u@(AVar _ s) = case M.lookup (u',p) m of
          Just res -> trace ("checked AVar " ++ show u) (c, res ++ l)
          Nothing | all (check sig p) reachables -> (Cache (M.insert (u', p) [] m), l)
                  | otherwise                    -> (Cache (M.insert (u', p) [u'] m), u':l)
                  where reachables = trace ("checking AVar " ++ show u) (getReachable sig s S.empty)
          where u' = AVar NoName s
        accuCheck (c@(Cache m), l) u@(Compl (AVar _ s) r) = case M.lookup (u',p) m of
          Just res -> (c, res ++ l)
          Nothing | all (check sig p) reachables -> (Cache (M.insert (u', p) [] m), l)
                  | otherwise                    -> (Cache (M.insert (u', p) [u'] m), u':l)
                  where reachables = trace ("checking Compl " ++ show u) (getReachable sig s (removePlusses r))
          where u' = Compl (AVar NoName s) r
        accuCheck (c, l) (Alias _ u) = accuCheck (c, l) u

-- check that t X p reduces to Bottom
-- with t a qaddt term and p a sum of constructor patterns
check :: Signature -> Term -> Term -> Bool
check _ Bottom _ = True
check sig p t = trace ("checking if BOTTOM: " ++ show t ++ " X " ++ show p) (checkConj (conjunction sig t p))
  where checkConj Bottom = True
        checkConj t = all (isBotMap . (getCheckMap sig (VarMap M.empty))) (removePlusses t)
-- check sig t (Plus p1 p2) = (check sig t p1) && (check sig t p2)



data Cache = Cache (M.Map (Term, Term) [Term])

emptyCache = Cache M.empty


-------------------------------- getReachable: --------------------------------

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
