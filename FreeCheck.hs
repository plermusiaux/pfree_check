module FreeCheck (checkTRS, Flag(..)) where

import Debug.Trace

import Control.Monad ( foldM, liftM )
import Data.Either
import Data.Maybe
import qualified Data.Map as M
import qualified Data.Set as S

import AlgoUtils ( isBottom, plus, removePlusses )
import Datatypes
import FreeCheckNL ( checkPfreeNL )
import Signature
import Reach ( getReachable )
import ReducePattern ( conjunction, normalizeSig, inferRules )



data Flag = Default
          | NonLinear             -- -p --non-linear
          | Linearized            -- -l --linear
          | Strict                -- -s --strict
          | Help                  -- -h --help
          deriving (Eq,Ord,Enum,Show,Bounded)


------------------------------------------------------------------------------

-- return the semantics equivalent of a term
buildEqui :: Flag -> Signature -> Cache -> Term -> (Cache, Term)
buildEqui flag sig c0 t@(Appl f ts)
  | isFunc sig f = (c2, AVar x (AType (range sig f) p))
  | otherwise    = (c1, Appl f equis)
  where (c1, equis) = foldr buildSub (c0, []) ts
        buildSub t (cache, l) = (cache', t':l)
          where (cache', t') = buildEqui flag sig cache t
        (c2, p) = foldl accuCheck (c1, Bottom) (profile sig f)
        accuCheck (cache, p) (qs, q) = case foldM subCheck cache (zip equis qs) of
          Right cache' -> (cache', plus p q)
          Left cache'  -> (cache', p)
        subCheck cache tp
          | null fails = Right cache' -- t is p-free
          | otherwise  = Left cache'  -- t is not p-free, stop subCheck computation
          where (cache', fails) = checkPfree flag sig cache tp
        x = case flag of Strict -> NoName
                         _      -> (VarName (show t))
buildEqui _ _ c t = (c, t)

------------------------------------------------------------------------------

-- check TRS : call checkRule for each rule and concatenate the results
-- return a map of failed rule with the terms that do not satisfy the expected pattern-free property
checkTRS :: Flag -> Signature -> [Rule] -> M.Map Rule (Term,[Term])
checkTRS flag sig rules = snd (foldl accuCheck (emptyCache, M.empty) rules)
  where nSig = normalizeSig sig
        accuCheck (c, m) rule
          | null fails = (c', m)
          | otherwise  = (c', M.union m fails)
          where (c', fails) = checkRule flag nSig c rule

-- check rule : for each profile of the head function symbol of the left hand side,
-- alias the variables in the right hand side and build its semantics equivalent,
-- then check that the term obtained verifies the corresponding pattern-free property.
-- return a list of terms that do not satisfy the expected pattern-free properties
checkRule :: Flag -> Signature -> Cache -> Rule -> (Cache, M.Map Rule (Term,[Term]))
checkRule Default sig c r = foldl accuCheck (c, M.empty) $ inferRules sig r
  where accuCheck (cache, m) (Rule lhs rhs, p)
          | isFLinear sig rhs = if null fails
                                then (cache2, m)
                                else (cache2, M.insert (Rule lhs equi) (p,fails) m)
          | nlcheck           = (cache, m)
          | otherwise         = (cache, M.insert (Rule lhs rhs) (p, [rhs]) m)
          where (cache1, equi) = buildEqui Default sig cache rhs
                (cache2, fails) = trace ("checking RULE " ++ show (Rule lhs equi)) $ checkPfree Default sig cache1 (equi,p)
                nlcheck = trace ("checking NL RULE " ++ show (Rule lhs rhs)) $ checkPfreeNL sig (rhs, p)
checkRule flag sig c r = foldl accuCheck (c, M.empty) $ inferRules sig r
  where accuCheck (cache, m) (Rule lhs rhs, p)
          | null fails = (cache2, m)
          | otherwise  = (cache2, M.insert (Rule lhs equi) (p,fails) m)
          where (cache1, equi) = buildEqui flag sig cache rhs
                (cache2, fails) = trace ("checking RULE " ++ show (Rule lhs equi)) $ checkPfree flag sig cache1 (equi,p)

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
                uVar = foldM (liftM . S.union) S.empty vts
                checkInter [] = True
                checkInter (h:tail) = case h of
                  Nothing  -> False
                  Just vti -> (checkInter tail) && (all check (catMaybes tail))
                                where check vtj = null (S.intersection vti vtj)

-- check that a term is p-free
-- parameters: Signature, Pattern p (should be a sum of constructor patterns), Rhs term of a rule (should be a qsymb)
-- return a list of terms that do not satisfy the expected pattern-free property
checkPfree :: Flag -> Signature -> Cache -> (Term, Term) -> (Cache, [Term])
checkPfree flag _ c0 (_, Bottom) = (c0, [])
checkPfree flag sig c0 (t, p) = accuCheck (c0, []) t
  where accuCheck (c@(Cache m), l) u@(Appl _ ts) = case M.lookup (u,p) m of
          Just res -> (c, res ++ l)
          Nothing | check flag sig p u -> (Cache (M.insert (u, p) lSub mSub), lSub ++ l)
                  | otherwise        -> (Cache (M.insert (u, p) (u:lSub) mSub), u:(lSub ++ l))
                  where (Cache mSub, lSub) = foldl accuCheck (c,[]) ts
        accuCheck (c@(Cache m), l) u@(AVar _ s) = case M.lookup (u',p) m of
          Just res -> trace ("checked AVar " ++ show u) (c, res ++ l)
          Nothing | all (check flag sig p) reachables -> (Cache (M.insert (u', p) [] m), l)
                  | otherwise                    -> (Cache (M.insert (u', p) [u'] m), u':l)
                  where reachables = trace ("checking AVar " ++ show u) $ getReachable sig s S.empty
          where u' = AVar NoName s
        accuCheck (c@(Cache m), l) u@(Compl (AVar _ s) r) = case M.lookup (u',p) m of
          Just res -> (c, res ++ l)
          Nothing | all (check flag sig p) reachables -> (Cache (M.insert (u', p) [] m), l)
                  | otherwise                    -> (Cache (M.insert (u', p) [u'] m), u':l)
                  where reachables = trace ("checking Compl " ++ show u) $ getReachable sig s (removePlusses r)
          where u' = Compl (AVar NoName s) r
        accuCheck (c, l) (Alias _ u) = accuCheck (c, l) u

-- check that t X p reduces to Bottom
-- with t a qaddt term and p a sum of constructor patterns
check :: Flag -> Signature -> Term -> Term -> Bool
check _ _ Bottom _ = True
check flag sig p t = trace ("checking if BOTTOM: " ++ show t ++ " X " ++ show p) $ checkConj (conjunction sig t p)
  where checkConj Bottom = True
        checkConj t = case flag of
          Linearized -> False
          _          -> all (isBotMap . (getCheckMap sig (VarMap M.empty))) (removePlusses t)
-- check sig t (Plus p1 p2) = (check sig t p1) && (check sig t p2)


------------------------------ check Variables: -------------------------------


data CheckMap = VarMap (M.Map VarName Term)
              | BotMap


isBotMap :: CheckMap -> Bool
isBotMap BotMap = True
isBotMap (VarMap vMap) = any isBottom vMap


checkGlue :: Signature -> Term -> Term -> Term
checkGlue _ Bottom _ = Bottom
checkGlue _ _ Bottom = Bottom
checkGlue sig (AVar _ _) t2 = t2
checkGlue sig t1 (AVar _ _) = t1
checkGlue sig t1 t2 = conjunction sig t1 t2

-- checkInsert :: Signature -> VarName -> Term -> CheckMap -> CheckMap
-- checkInsert _ _ _ BotMap = BotMap
-- checkInsert sig x t@(AVar _ _) (VarMap vMap) = VarMap (M.insertWith (\u _ -> u) x t vMap)
-- checkInsert sig x t (VarMap vMap) = case M.lookup x vMap of
--   Nothing -> VarMap (M.insert x t vMap)
--   Just u  -> case conjunction sig t u of
--                Bottom -> BotMap
--                txu    -> VarMap (M.insert x txu vMap)

getCheckMap :: Signature -> CheckMap -> Term -> CheckMap
getCheckMap _ BotMap _ = BotMap
getCheckMap _ cMap (AVar NoName _) = cMap
getCheckMap _ cMap (Compl (AVar NoName _) _) = cMap
getCheckMap sig cMap (Appl f ts) = foldl (getCheckMap sig) cMap ts
getCheckMap sig (VarMap vMap) t = VarMap m
  where m = case t of
              AVar x _             -> M.insertWith (checkGlue sig) x t vMap
              Alias x u            -> M.insertWith (checkGlue sig) x u vMap
-- getCheckMap sig cMap v@(AVar x _) = checkInsert sig x (v, []) cMap
-- getCheckMap sig cMap (Alias x u) = checkInsert sig x (u, []) cMap


------------------------------------------------------------------------------


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
