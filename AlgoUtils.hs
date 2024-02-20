module AlgoUtils ( buildVar, checkDiff, collect, interleave, isBottom,
                   linearize, plus, removePlusses, sumTerm ) where

import qualified Data.Set as S

import Datatypes

--------------------------------- From Algo: ----------------------------------

checkDiff :: Eq a => [a] -> [a] -> Maybe [a]
checkDiff l [] = Just l
checkDiff [] _ = Nothing
checkDiff (q1:l1) l2@(q2:tail)
  | q1 == q2  = checkDiff l1 tail
  | otherwise = (q1:) <$> (checkDiff l1 l2)


-- interleave abc ABC = Abc, aBc, abC
interleave :: [a] -> [a] -> [[a]]
interleave [] [] = []
interleave (xi:xs) (yi:ys) = (yi:xs) : (map (xi:) (interleave xs ys))


buildVar :: TypeName -> Term -> Term
buildVar s p = AVar NoName (AType s p)


collect :: Term -> [Term]
collect (AVar _ (AType s p)) = [p]
collect (Plus t1 t2) = (collect t1) ++ (collect t2)


isBottom :: Term -> Bool
isBottom Bottom = True
isBottom _ = False


linearize :: Term -> Term
linearize (Alias x u) = linearize u
linearize (Compl (AVar x s) r) = Compl (AVar NoName s) r
linearize (AVar x s) = AVar NoName s
linearize t = t


plus :: Term -> Term -> Term
plus Bottom u = u                                                         --A1
plus t Bottom = t                                                         --A2
plus t u = Plus t u

sumTerm :: Foldable t => t Term -> Term
sumTerm = foldr plus Bottom

removePlusses :: Term -> S.Set Term
removePlusses (Plus p1 p2) = removePlusses p1 `S.union` removePlusses p2
removePlusses (Appl f ps) = S.mapMonotonic (Appl f) subterms              --S1
  where subterms = foldr buildSet (S.singleton []) ps
        buildSet t = S.mapMonotonic (uncurry (:)) . S.cartesianProduct (removePlusses t)
removePlusses Bottom = S.empty
removePlusses v@(AVar _ _) = S.singleton v
removePlusses m@(Compl _ _) = S.singleton m
removePlusses a@(Alias x p) = S.map (Alias x) (removePlusses p)










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

