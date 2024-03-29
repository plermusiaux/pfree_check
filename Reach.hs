module Reach ( computeQc, getReachable, isInstantiable ) where

import Control.Monad ( foldM )
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
getReachable sig (AType s p) = S.map buildComplement . getReach sig s p
  where buildComplement (Reach s' p')
          | null p'   = (AVar NoName (AType s' p))
          | otherwise = Compl (AVar NoName (AType s' p)) (sumTerm p')

-- abandon hope all ye who enter here
getReach :: Signature -> TypeName -> Term -> S.Set Term -> S.Set Reach
getReach sig s0 p = \r0 ->
    if any isVar r0 then S.empty --computeQc filters out variables, so we just need to do this for r0
    else fromMaybe S.empty (computeReach S.empty (Reach s0 r0))
  where pSet = removePlusses p
        computeReach sReach sr@(Reach s r)
          | S.member sr sReach = Just sReach
          | otherwise          = foldl accuReach Nothing (ctorsOfRange sig s)
          where r' | hasType sig p s = S.union r pSet
                   | otherwise       = r
                reach' = S.insert sr sReach
                accuReach dReach c = foldl accuSubReach dReach (computeQc sig c r')
                  where d = domain sig c
                        accuSubReach rReach q = case foldM computeReach mReach dq of
                          Nothing -> rReach
                          just    -> just
                          where dq = zipWith Reach d q
                                mReach = fromMaybe reach' rReach

isInstantiable :: Signature -> TypeName -> Term -> S.Set Term -> Bool
isInstantiable = getReachMin

-- stops when proof that the semantics is not empty
getReachMin :: Signature -> TypeName -> Term -> S.Set Term -> Bool
getReachMin sig s0 p = \r0 ->
    all (not.isVar) r0 && isJust (computeReach S.empty (Reach s0 r0))
  where pSet = removePlusses p
        computeReach sReach sr@(Reach s r)
          | S.member sr sReach = Just sReach
          | otherwise          = listToMaybe (mapMaybe accuReach (ctorsOfRange sig s))
          where r' | hasType sig p s = S.union r pSet
                   | otherwise       = r
                reach' = S.insert sr sReach
                accuReach c = listToMaybe (mapMaybe accuSubReach (computeQc sig c r'))
                  where d = domain sig c
                        accuSubReach q = foldM computeReach reach' (zipWith Reach d q)

-- return all possible distributions of r over c
computeQc :: Signature -> FunName -> (S.Set Term) -> [[S.Set Term]]
computeQc sig c = foldr getDist [replicate (arity sig c) S.empty]
  where getDist (Appl g ts) tQc
          | c == g    = concatMap (`distribute` ts) tQc
          | otherwise = tQc

distribute :: [S.Set Term] -> [Term] -> [[S.Set Term]]
distribute [] [] = []
distribute (qi:ql) (ti:tl)
  | isVar ti  = tail -- filter out variables to avoid empty semantics
  | otherwise = ((S.insert ti qi) : ql) : tail
  where tail = map (qi:) (distribute ql tl)

isVar :: Term -> Bool
isVar (AVar _ _)   = True
isVar (Plus t1 t2) = (isVar t1) || (isVar t2)
isVar _            = False

