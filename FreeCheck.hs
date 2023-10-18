module FreeCheck (checkTRS, Flag(..)) where

import Control.Monad ( foldM, liftM )
import Data.Either
import Data.Foldable ( foldrM )
import Data.Maybe
import qualified Data.Map as M
import qualified Data.Set as S
import Text.Printf ( printf )

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
buildEqui :: Flag -> Signature -> Cache -> Term -> IO (Cache, Term)
buildEqui flag sig c0 t@(Appl f ts) = do
  (c1, equis) <- foldrM buildSub (c0, []) ts
  if isFunc sig f then do
    (c2, p) <- foldM (accuCheck equis) (c1, Bottom) (profile sig f)
    return (c2, AVar x (AType (range sig f) p))
  else return (c1, Appl f equis)
  where buildSub t (cache, l) = (\(c', t') -> (c', t':l)) <$> buildEqui flag sig cache t
        accuCheck equis (cache, p) (qs, q) = do
          (cache', b) <- subCheck cache (zip equis qs)
          if b then return (cache', plus p q)
          else return (cache', p)
        subCheck cache [] = return (cache, True)
        subCheck cache (tp:l) = do
          (cache', fails) <- checkPfree flag sig cache tp
          if null fails then subCheck cache' l  -- t is p-free
          else return (cache', False)           -- t is not p-free, stop subCheck computation
        x = case flag of Strict -> NoName
                         _      -> (VarName (show t))
buildEqui _ _ c t = return (c, t)

------------------------------------------------------------------------------

-- check TRS : call checkRule for each rule and concatenate the results
-- return a map of failed rule with the terms that do not satisfy the expected pattern-free property
checkTRS :: Flag -> Signature -> [Rule] -> IO (M.Map Rule (Term,[Term]))
checkTRS flag sig rules = snd <$> foldM accuCheck (emptyCache, M.empty) rules
  where nSig = normalizeSig sig
        accuCheck (c, m) rule = do
          (c', fails) <- checkRule flag nSig c rule
          if null fails then return (c', m)
          else return (c', M.union m fails)

-- check rule : for each profile of the head function symbol of the left hand side,
-- alias the variables in the right hand side and build its semantics equivalent,
-- then check that the term obtained verifies the corresponding pattern-free property.
-- return a list of terms that do not satisfy the expected pattern-free properties
checkRule :: Flag -> Signature -> Cache -> Rule -> IO (Cache, M.Map Rule (Term,[Term]))
checkRule Default sig c r = foldM accuCheck (c, M.empty) $ inferRules sig r
  where accuCheck (cache, m) (Rule lhs rhs, p) =
          if isFLinear sig rhs then do
            (cache1, equi) <- buildEqui Default sig cache rhs
            printf "checking RULE %v\n" (Rule lhs equi)
            (cache2, fails) <- checkPfree Default sig cache1 (equi,p)
            if null fails then return (cache2, m)
            else return (cache2, M.insert (Rule lhs equi) (p,fails) m)
          else do
            printf "checking RULE %v\n" (Rule lhs rhs)
            b <- checkPfreeNL sig (rhs, p)
            if b then return (cache, m)
            else return (cache, M.insert (Rule lhs rhs) (p, [rhs]) m)
checkRule flag sig c r = foldM accuCheck (c, M.empty) $ inferRules sig r
  where accuCheck (cache, m) (Rule lhs rhs, p) = do
          (cache1, equi) <- buildEqui flag sig cache rhs
          printf "checking RULE %v\n" (Rule lhs equi)
          (cache2, fails) <- checkPfree flag sig cache1 (equi,p)
          if null fails then return (cache2, m)
          else return (cache2, M.insert (Rule lhs equi) (p,fails) m)

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
checkPfree :: Flag -> Signature -> Cache -> (Term, Term) -> IO (Cache, [Term])
checkPfree flag _ c0 (_, Bottom) = return (c0, [])
checkPfree flag sig c0 (t, p) = accuCheck (c0, []) t
  where accuCheck (c@(Cache m), l) u@(Appl _ ts) = case M.lookup (u,p) m of
          Just res -> return (c, res ++ l)
          Nothing  -> do
            b <- check flag sig p u
            (Cache mSub, lSub) <- foldM accuCheck (c,[]) ts
            if b then return (Cache (M.insert (u, p) lSub mSub), lSub ++ l)
            else return (Cache (M.insert (u, p) (u:lSub) mSub), u:(lSub ++ l))
        accuCheck (c@(Cache m), l) u@(AVar _ s) = case M.lookup (u',p) m of
          Just res -> (c, res ++ l) <$ printf "checked AVar %v\n" u
          Nothing -> do
            printf "checking AVar %v\n" u
            b <- foldr checkAll (pure True) $ getReachable sig s S.empty
            if b then return (Cache (M.insert (u', p) [] m), l)
            else return (Cache (M.insert (u', p) [u'] m), u':l)
          where u' = AVar NoName s
        accuCheck (c@(Cache m), l) u@(Compl (AVar _ s) r) = case M.lookup (u',p) m of
          Just res -> return (c, res ++ l)
          Nothing -> do
            printf "checking Compl %v\n" u
            b <- foldr checkAll (pure True) $ getReachable sig s (removePlusses r)
            if b then return (Cache (M.insert (u', p) [] m), l)
            else return  (Cache (M.insert (u', p) [u'] m), u':l)
          where u' = Compl (AVar NoName s) r
        accuCheck cl (Alias _ u) = accuCheck cl u
        checkAll u mb = do
          b <- check flag sig p u
          if b then mb else return False

-- check that t X p reduces to Bottom
-- with t a qaddt term and p a sum of constructor patterns
check :: Flag -> Signature -> Term -> Term -> IO Bool
check _ _ Bottom _ = return True
check flag sig p t =
  checkConj (conjunction sig t p) <$ printf "checking if BOTTOM: %v X %v\n" t p
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
