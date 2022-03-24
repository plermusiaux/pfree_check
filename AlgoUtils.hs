module AlgoUtils ( collect, interleave, isBottom, linearize,
                   plus, removePlusses, sumTerm ) where

import Control.Monad ( mapM )
import qualified Data.Set as S

import Datatypes

--------------------------------- From Algo: ----------------------------------

isBottom :: Term -> Bool
isBottom Bottom = True
isBottom _ = False


plus :: Term -> Term -> Term
plus Bottom u = u                                                         --A1
plus t Bottom = t                                                         --A2
plus t u = Plus t u

sumTerm :: Foldable t => t Term -> Term
sumTerm = foldr plus Bottom

removePlusses :: Term -> S.Set Term
removePlusses (Plus p1 p2) = removePlusses p1 `S.union` removePlusses p2
removePlusses (Appl f ps) = S.fromList (map (Appl f) subterms)            --S1
  where subterms = mapM (S.toList . removePlusses) ps
--   where subterms = foldr buildSet (S.singleton []) ps
--         buildSet t sl = foldr (S.union . (buildList t)) S.empty sl
--         buildList t l = S.mapMonotonic (:l) (removePlusses t)
--
--         buildSet t sl = S.mapMonotonic (uncurry (:)) (S.cartesianProduct (removePlusses t) sl)
removePlusses Bottom = S.empty
removePlusses v@(AVar _ _) = S.singleton v
removePlusses m@(Compl _ _) = S.singleton m
removePlusses a@(Alias x p) = S.map (Alias x) (removePlusses p)


-- interleave abc ABC = Abc, aBc, abC
interleave :: [a] -> [a] -> [[a]]
interleave [] [] = []
interleave (xi:xs) (yi:ys) = (yi:xs) : (map (xi:) (interleave xs ys))


collect :: Term -> [Term]
collect (AVar _ (AType s p)) = [p]
collect (Plus t1 t2) = (collect t1) ++ (collect t2)

linearize :: Term -> Term
linearize (Alias x u) = linearize u
linearize (Compl (AVar x s) r) = Compl (AVar NoName s) r
linearize (AVar x s) = AVar NoName s
linearize t = t















----------------------------- not used anymore --------------------------------
-- typeVariables :: Signature -> [Rule] -> [Rule]
-- typeVariables sig rules = map (inferVarType sig) rules
-- 
-- inferVarType :: Signature -> Rule -> Rule
-- inferVarType sig (Rule lhs rhs) = Rule lhs (replaceVar varMap rhs)
--   where replaceVar m (Appl f ts) = Appl f (map (replaceVar m) ts)
--         replaceVar m (AVar x Unknown) = m M.! x
--         varMap = getVarMap M.empty lhs
--           where getVarMap m (Appl f ts) = foldl getVarMap (updateMap ts f m) ts
--                 getVarMap m _ = m
--                 updateMap ts f m = foldl mapVariables m (zip ts (domain sig f))
--                   where mapVariables m ((AVar x _), s) = M.insert x (AVar x (AType s Bottom)) m
--                         mapVariables m _ = m

