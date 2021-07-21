module Reach ( computeQc, getReachable, isInstantiable ) where

import Data.Maybe
import qualified Data.Set as S

import AlgoUtils ( removePlusses, sumTerm )
import Datatypes
import Signature

data Reach = Reach TypeName (S.Set Term)
  deriving (Eq, Ord)

-- Burn After Reading
--instance Show Reach where
--  show (Reach s r) | null r    = "x : " ++ show s ++ " \\ bot"
--                   | otherwise = "x : " ++ show s ++ " \\ (" ++ (concatMap show r) ++ ")"
--

getReachable :: Signature -> AType -> S.Set Term -> S.Set Term
getReachable sig (AType s p) r = S.map buildComplement reaches
  where reaches = getReach sig s p r
        buildComplement (Reach s' p')
          | null p'   = (AVar NoName (AType s' p))
          | otherwise = Compl (AVar NoName (AType s' p)) (sumTerm p')

-- abandon hope all ye who enter here
getReach :: Signature -> TypeName -> Term -> S.Set Term -> S.Set Reach
getReach sig s0 p r0
  | any isVar r0 = S.empty --computeQc filters out variables, so we just need to do this for r0
  | otherwise    = computeReach s0 r0 S.empty
  where pSet = removePlusses p
        recCompute (si, qi) next dReach
          | null iReach = iReach -- not computing more reach when one qi has already failed
          | otherwise   = next iReach -- sequentially computing reaches to avoid performing unions
          where iReach = computeReach si qi dReach
        computeReach s r sReach
          | S.member (Reach s r) sReach = sReach
          | otherwise                   = fromMaybe S.empty (foldl accuReach Nothing (ctorsOfRange sig s))
          where r' | hasType sig p s = S.union r pSet
                   | otherwise       = r
                reach' = S.insert (Reach s r) sReach
                accuReach dReach c = foldl accuSubReach dReach (computeQc sig c r')
                  where d = domain sig c
                        accuSubReach rReach q
                          | null tReach = rReach -- ignores result when empty, ie not instantiable
                          | otherwise   = Just tReach
                          where tReach = (foldr recCompute id (zip d q)) (fromMaybe reach' rReach)

isInstantiable :: Signature -> TypeName -> Term -> S.Set Term -> Bool
isInstantiable sig s p r = not (null (getReachMin sig s p r))

-- stops when proof that the semantics is not empty
getReachMin :: Signature -> TypeName -> Term -> S.Set Term -> S.Set Reach
getReachMin sig s0 p r0
  | any isVar r0 = S.empty
  | otherwise    = computeReach s0 r0 S.empty
  where pSet = removePlusses p
        recCompute (si, qi) next rReach
          | null iReach = iReach
          | otherwise   = next iReach
          where iReach = computeReach si qi rReach
        computeReach s r sReach
          | S.member (Reach s r) sReach = sReach
          | otherwise                   = foldr accuReach S.empty (ctorsOfRange sig s)
          where r' | hasType sig p s = S.union r pSet
                   | otherwise       = r
                reach' = S.insert (Reach s r) sReach
                accuReach c dReach
                  | null qReach = dReach
                  | otherwise   = qReach
                  where qReach = foldr accuSubReach S.empty (computeQc sig c r')
                        d = domain sig c
                        accuSubReach q rReach
                          | null tReach = rReach
                          | otherwise   = tReach
                          where tReach = (foldr recCompute id (zip d q)) reach'

computeQc :: Signature -> FunName -> (S.Set Term) -> [[S.Set Term]]
computeQc sig c r = foldr getDist [replicate (length d) S.empty] r
  where getDist (Appl g ts) tQc
          | c == g    = concatMap accuDist tQc
          | otherwise = tQc
          where accuDist q = distribute q ts
                distribute [] [] = []
                distribute (qi:ql) (ti:tl)
                  | isVar ti  = tail -- filter out variables to avoid empty semantics
                  | otherwise = ((S.insert ti qi) : ql) : tail
                  where tail = map (qi:) (distribute ql tl)
        d = domain sig c

isVar :: Term -> Bool
isVar (AVar _ _)   = True
isVar (Plus t1 t2) = (isVar t1) || (isVar t2)
isVar _            = False

