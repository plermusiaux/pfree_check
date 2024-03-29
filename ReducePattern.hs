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
alias x Bottom = Bottom                                                   --L1
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
    Alias x p1 \\ p2 = alias x (p1 \\ p2)                                 --L3
--    p1 \\ Alias x p2 = p1 \\ p2

-------------------------------------------------------------------------------

conjunction :: Signature -> Term -> Term -> Term
conjunction sig = (*)
  where
    Bottom * u = Bottom                                                   --E2
    u * Bottom = Bottom                                                   --E3
    (Plus u1 u2) * u = plus (u1 * u) (u2 * u)                             --S2
    u * (Plus u1 u2) = plus (u * u1) (u * u2)                             --S3
    (AVar x Unknown) * (AVar _ s) = Alias x (AVar NoName s) -- for variable inference only
    u * (AVar _ (AType _ Bottom)) = u                                     --Generalization of T1
    v@(AVar x (AType s1 p1)) * (AVar _ s@(AType s2 p2))
      | s1 /= s2     = Bottom
      | p1 == p2     = v                                                  --T2
      | p1 == Bottom = AVar x s                                           --T1
--    | otherwise    -> (AVar x (AType s1 (Plus p1 p2)))
-- This should never happen, check isInstantiable sig s1 (plus p1 p2) S.empty, if it does...
    (AVar x (AType s Bottom)) * u
        | hasType sig u s = alias x u                                     --Generalization of T2
        | otherwise       = Bottom
    Appl f ps * Appl g qs
        | f == g = appl f (zipWith (*) ps qs)                             --T3
        | otherwise = Bottom                                              --T4
    (AVar x (AType s p)) * (Appl f ts)
        | s == s'   = complement sig (alias x (appl f zXts)) p            --P1
        | otherwise = Bottom
        where (d, s') = sigOf sig f
              zXts = zipWith ((*) . (`buildVar` p)) d ts
    (Appl f ts) * (AVar x (AType s p))
        | s == s'   = complement sig (appl f tXzs) p                      --P2
        | otherwise = Bottom
        where (d, s') = sigOf sig f
              tXzs = zipWith (\ti -> (ti *) . (`buildVar` p)) ts d
    v1 * (Compl v2 t) = complement sig (v1 * v2) t                        --P3-4
    (Compl v t) * u = complement sig (v * u) t                            --P5
    (Alias x t) * u = alias x (t * u)                                     --L4
    t * (Alias x u) = alias x (t * u)                                     --L5



-- type and put all annotations in qaddt form
normalizeSig :: Signature -> Signature
normalizeSig sig@(Signature ctors funs) = Signature ctors tFuns
  where tFuns = map normF funs
        normF (Function f d r pr) = (Function f d r (map (normPr d r) pr))
        normPr d r (qs, p) = (map reduce $ zipWith (#) qs d, reduce $ p # r)
        reduce b@Bottom = b
        reduce v@(AVar _ _) = v
        reduce (Plus u1 u2) = Plus (reduce u1) (reduce u2)
        reduce (Compl u v) = complement sig (reduce u) (reduce v)
        reduce (Appl g tl) = sumTerm $ removePlusses (Appl g (map reduce tl))
        b@Bottom # _ = b
        (Plus u1 u2) # s = Plus (u1 # s) (u2 # s)
        (Appl g tl)  # _  = Appl g (zipWith (typeCheck sig) tl (domain sig g))
        t # s = typeCheck sig t s

-- for each profile of the annotated symbol of the lhs,
-- infer, as qaddt patterns, the possible shapes of the variables
-- such that the lhs verifies the expected pattern-free properties.
-- for all possible inference, generate the corresponding rhs
-- by replacing the corresponding variables with the inferred pattern.
-- the obtained rhs patterns are qsymb
replaceVariables :: Signature -> Rule -> [Rule]
replaceVariables sig r@(Rule lhs rhs) = foldl accuRule [] (removePlusses lhs)
  where accuRule l lhs
          | any isBottom varMap = l -- if a variable has conflicting instances (PL: do we really need to test?)
          | otherwise           = (Rule lhs (replaceVar varMap rhs)) : l
          where varMap = getVarMap lhs
        getVarMap t@(Alias x _) = M.singleton x t
        getVarMap (Appl g ts) = M.unionsWith (conjunction sig) (map getVarMap ts)
        getVarMap (AVar x s) = M.singleton x (Alias x (AVar NoName s))
        getVarMap (Compl (AVar x s) r) = M.singleton x (Alias x (Compl (AVar NoName s) r))
        replaceVar m (Appl f ts) = Appl f (map (replaceVar m) ts)
        replaceVar m (AVar x Unknown) = case M.lookup x m of
          Just t  -> t
          Nothing -> error $ printf "variable %v unknown in rhs of rule:\n\t%v" x r


inferRules :: Signature -> Rule -> [(Rule, Term)]
inferRules sig (Rule (Appl f ls0) rhs0) = concatMap buildRules (map buildDomain (profile sig f))
  where buildDomain (qs, p) = (zipWith AType d qs, p)
        buildRules (_, Bottom) = []
        buildRules (ad, p) = map (buildRule p) (replaceVariables sig (Rule lhs rhs0))
          where lhs = Appl f (zipWith conjVar ls ad)
        buildRule p (Rule l rhs) = (Rule l (typeCheck sig rhs s), p)
        conjVar t a = conjunction sig t (AVar NoName a)
        ls = zipWith (typeCheck sig) ls0 d
        (d, s) = sigOf sig f

