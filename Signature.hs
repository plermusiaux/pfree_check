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
  pfree,
  arity,
  ctorsOfRange,
  ctorsOfSameRange,
  hasType,
  isFunc
) where

import Datatypes (FunName(..), TypeName, Constructor(..), Function(..), Signature(..), Term(..))
import Data.List ( foldl )
import Data.Maybe

_funName (Constructor f _ _) = f

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
        getF (Function g d _ _)
          | f == g    = Just d
          | otherwise = Nothing

range :: Signature -> FunName -> TypeName
range sig f = getter getC getF sig f
  where getC (Constructor g _ r)
          | f == g    = Just r
          | otherwise = Nothing
        getF (Function g _ r _)
          | f == g    = Just r
          | otherwise = Nothing

pfree :: Signature -> FunName -> Term
pfree sig f = getter getC getF sig f
  where getC _ = Nothing
        getF (Function g _ _ p)
          | f == g    = Just p
          | otherwise = Nothing

arity :: Signature -> FunName -> Int
arity sig f = length (domain sig f)

ctorsOfRange :: Signature -> TypeName -> [FunName]
ctorsOfRange (Signature ctors _) ty = map _funName (filter hasRangeTy ctors)
  where hasRangeTy (Constructor _ _ ty' ) = ty == ty'

ctorsOfSameRange :: Signature -> FunName -> [FunName]
ctorsOfSameRange sig f = ctorsOfRange sig (range sig f)

hasType :: Signature -> Term -> TypeName -> Bool
hasType sig (Appl f _) s = range sig f == s
hasType sig (Alias _ t) s = hasType sig t s
hasType sig Bottom _ = False
hasType sig (AVar _ _ s1) s2 = s1 == s2

isFunc :: Signature -> FunName -> Bool
isFunc (Signature _ funs) f = any isF funs
  where isF (Function g _ _ _) = f==g
