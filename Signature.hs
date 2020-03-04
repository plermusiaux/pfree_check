-- Copyright 2015 Google Inc. All Rights Reserved.
--
-- Licensed under the Apache License, Version 2.0 (the "License")--
-- you may not use this file except in compliance with the License.
-- You may obtain a copy of the License at
--
--     http://www.apache.org/licenses/LICENSE-2.0
--
-- Unless required by applicable law or agreed to in writing, software
-- distributed under the License is distributed on an "AS IS" BASIS,
-- WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
-- See the License for the specific language governing permissions and
-- limitations under the License.

module Signature (
  domain,
  range,
  aDomain,
  aRange,
  pfree,
  arity,
  ctorsOfRange,
  ctorsOfSameRange,
  hasType,
  isFunc
) where

import Datatypes (FunName(..), TypeName, Constructor(..), Function(..), Signature(..), Term(..), AType(..))
import Data.List ( foldl )
import Data.Maybe

_funName (Constructor f _ _) = f

_typeName (AType s _) = s
_pfree (AType _ p) = p

getterF :: (Function -> Maybe a) -> Signature -> FunName -> a
getterF get (Signature _ funs) f = try (foldl (wrap get) Nothing funs)
  where try (Just r) = r
        try Nothing = error (show f ++ " is not declared")
        wrap get Nothing g = get g
        wrap _ j _ = j

getter :: (Constructor -> Maybe a) -> (Function -> Maybe a) -> Signature -> FunName -> a
getter getC getF (Signature ctors funs) f = try (foldl (wrap getC) (foldl (wrap getF) Nothing funs) ctors)
  where try (Just r) = r
        try Nothing = error (show f ++ " is not declared")
        wrap get Nothing g = get g
        wrap _ j _ = j

domain :: Signature -> FunName -> [TypeName]
domain sig f = getter getC getF sig f
  where getC (Constructor g d _)
          | f == g    = Just d
          | otherwise = Nothing
        getF (Function g d _)
          | f == g    = Just (map _typeName d)
          | otherwise = Nothing

range :: Signature -> FunName -> TypeName
range sig f = getter getC getF sig f
  where getC (Constructor g _ r)
          | f == g    = Just r
          | otherwise = Nothing
        getF (Function g _ r)
          | f == g    = Just (_typeName r)
          | otherwise = Nothing

aDomain :: Signature -> FunName -> [AType]
aDomain sig f = getterF get sig f
  where get (Function g d _)
          | f == g    = Just d
          | otherwise = Nothing

aRange :: Signature -> FunName -> AType
aRange sig f = getterF get sig f
  where get (Function g _ r)
          | f == g    = Just r
          | otherwise = Nothing

pfree :: Signature -> FunName -> Term
pfree sig f = getterF get sig f
  where get (Function g _ r)
          | f == g    = Just (_pfree r)
          | otherwise = Nothing

arity :: Signature -> FunName -> Int
arity sig f = length (domain sig f)

ctorsOfRange :: Signature -> TypeName -> [FunName]
ctorsOfRange (Signature ctors _) ty = map _funName (filter hasRangeTy ctors)
  where hasRangeTy (Constructor _ _ ty' ) = ty == ty'

ctorsOfSameRange :: Signature -> FunName -> [FunName]
ctorsOfSameRange sig f = ctorsOfRange sig (range sig f)

hasType :: Signature -> Term -> TypeName -> Bool
hasType sig t s = t # s
  where
    (Appl f _) # so = range sig f == so
    (Alias _ u) # so = u # so
    Bottom # _ = False
    (AVar _ (AType s1 _)) # s2 = s1 == s2
    (Compl u _) # so = u # so

isFunc :: Signature -> FunName -> Bool
isFunc (Signature _ funs) f = any isF funs
  where isF (Function g _ _) = f==g
