module ReducePattern ( alias, appl, complement, conjunction, normalizeSig, inferRules ) where

import qualified Data.Map as M
import qualified Data.Set as S

import Text.Printf ( printf )

import AlgoUtils ( buildVar, interleave, isBottom, plus, removePlusses, sumTerm )
import Datatypes
import Reach ( isInstantiable )
import Signature

------------------------------------------------------------------------------

alias :: VarName -> Term -> Term
alias NoName t = t
alias x Bottom = Bottom
alias x t = Alias x t

appl :: FunName -> [Term] -> Term
appl f ps | any isBottom ps = Bottom                                      --E1
          | otherwise = Appl f ps

------------------------------------------------------------------------------

complement :: Signature -> Term -> Term -> Term
complement sig = (\\)
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
        | f /= g || someUnchanged = Appl f ps                             --M8
        | otherwise = sumTerm [appl f ps' | ps' <- interleave ps pqs]     --M7
      where pqs = zipWith (\\) ps qs
            someUnchanged = or (zipWith (==) ps pqs)
    (Compl v t) \\ u = v \\ (plus t u)                                    --P6
    v@(AVar x sp@(AType s p)) \\ t
        | isBottom p               = sumTerm [pattern c \\ t | c <- cs]
        | isInstantiable sig s p r = alias x (Compl (AVar NoName sp) t)
        | otherwise                = Bottom                               --P7
        where cs = ctorsOfRange sig s
              pattern c = Appl c (map (`buildVar` p) (domain sig c))
              r = removePlusses t
    Alias x p1 \\ p2 = alias x (p1 \\ p2)
--    p1 \\ Alias x p2 = p1 \\ p2

-------------------------------------------------------------------------------

conjunction :: Signature -> Term -> Term -> Term
conjunction sig = (*)
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
--              pattern a = Appl a (map (`buildVar` p) (domain sig a))
    (AVar x (AType s p)) * (Appl f ts)
        | s == range sig f = complement sig (alias x (appl f zXts)) p    --P1
        | otherwise        = Bottom
        where zXts = zipWith ((*) . (`buildVar` p)) (domain sig f) ts
    (Appl f ts) * (AVar x (AType s p))
        | s == range sig f = complement sig (appl f tXzs) p              --P2
        | otherwise        = Bottom
        where tXzs = zipWith (\ti -> (ti *) . (`buildVar` p)) ts (domain sig f)
    v1 * (Compl v2 t) = complement sig (v1 * v2) t                       --P3-4
    (Compl v t) * u = complement sig (v * u) t                           --P5
--    (Var x) * u = Alias x u
--    (Appl f ts) * (AVar _ (AType _ p)) = complement sig (Appl f tsXz) p
--        where tsXz = zipWith conjVar ts (domain sig f)
--              conjVar t s = t * (AVar (VarName (show t)) (AType s p))
--
    (Alias x t) * u = alias x (t * u)
    t * (Alias x u) = alias x (t * u)



-- type and put all annotations in qaddt form
normalizeSig :: Signature -> Signature
normalizeSig sig@(Signature ctors funs) = Signature ctors tFuns
  where tFuns = map normF funs
        normF (Function f d r pr) = (Function f d r (map normPr pr))
          where normPr (qs, p) = (map reduce $ zipWith (#) qs d, reduce $ p # r)
        reduce Bottom = Bottom
        reduce v@(AVar _ _) = v
        reduce (Plus u1 u2) = Plus (reduce u1) (reduce u2)
        reduce (Compl u v) = complement sig (reduce u) (reduce v)
        reduce (Appl g tl) = sumTerm $ removePlusses (Appl g (map reduce tl))
        Bottom # _ = Bottom
        (AVar x Unknown) # so      = AVar x (AType so Bottom)
        v@(AVar x (AType _ _)) # _ = v
        (Anti u)     # so = Compl (AVar NoName (AType so Bottom)) (u # so)
        (Compl u v)  # so = Compl (u # so) (v # so)
        (Plus u1 u2) # so = Plus (u1 # so) (u2 # so)
        (Appl g tl)  # _  = Appl g (zipWith (#) tl (domain sig g))

-- for each profile of the annotated symbol of the lhs,
-- infer, as qaddt patterns, the possible shapes of the variables
-- such that the lhs verifies the expected pattern-free properties.
-- for all possible inference, generate the corresponding rhs
-- by replacing the corresponding variables with the inferred pattern.
-- the obtained rhs patterns are qsymb
replaceVariables :: Signature -> Rule -> [AType] -> [Rule]
replaceVariables sig r@(Rule (Appl f ls) rhs) d = foldl accuRule [] lterms
  where lterms = removePlusses (Appl f subLterms)
        subLterms = zipWith conjVar ls d
        conjVar t s = conjunction sig t (AVar NoName s)
        accuRule l lhs
          | any isBottom varMap = l -- if a variable has conflicting instances (PL: do we really need to test?)
          | otherwise           = (Rule lhs (typeCheck sig ((replaceVar varMap) rhs) s)):l
          where varMap = getVarMap lhs s -- c(ti) * x^-bot is reduced to c(ti) so we build the annotated sorts manually for variables of ti
        getVarMap t@(Alias x _) _ = M.singleton x t
        getVarMap (Appl g ts) _ = M.unionsWith (conjunction sig) (zipWith getVarMap ts (domain sig g))
        getVarMap (AVar x _) s = M.singleton x (Alias x (AVar NoName (AType s Bottom)))
        getVarMap (Compl (AVar x _) r) s = M.singleton x (Alias x (Compl (AVar x (AType s Bottom)) r))
        replaceVar m (Appl f ts) = Appl f (map (replaceVar m) ts)
        replaceVar m (AVar x Unknown) = case M.lookup x m of
          Just t  -> t
          Nothing -> error $ printf "variable %v unknown in rhs of rule:\n\t%v" x r
        s = range sig f


inferRules :: Signature -> Rule -> [(Rule, Term)]
inferRules sig r@(Rule (Appl f _) _) = concatMap buildRule (map buildDomain (profile sig f))
  where buildRule (_, Bottom) = []
        buildRule (ad, p) = zip (replaceVariables sig r ad) (repeat p)
        buildDomain (qs, p) = (zipWith AType d qs, p)
        d = domain sig f

