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

import Datatypes (FunName, TypeName, Constructor(..), Function(..), Signature(..), Term(..), AType(..))
import Data.List ( find )
import Data.Either

_funName (Constructor f _ _) = f
_Cdomain (Constructor _ d _) = d
_Crange (Constructor _ _ r) = r

_Fdomain (Function _ d _) = d
_Frange (Function _ _ r) = r

_typeName (AType s _) = s
_pfree (AType _ p) = p

getFunction :: Signature -> FunName -> Function
getFunction (Signature _ funs) f = try (find isF funs)
  where try (Just r) = r
        try Nothing = error (show f ++ " is not declared")
        isF (Function g _ _) = f == g

getter :: (Constructor -> a) -> (Function -> a) -> Signature -> FunName -> a
getter getC getF (Signature ctors funs) f = unpack (find isF eithers)
  where unpack (Just r) = either getC getF r
        unpack Nothing = error (show f ++ " is not declared")
        eithers = (map Left ctors) ++ (map Right funs)
        isF (Left (Constructor g _ _)) = f == g
        isF (Right (Function g  _ _)) = f == g

domain :: Signature -> FunName -> [TypeName]
domain sig f = getter _Cdomain ((map _typeName)._Fdomain) sig f

range :: Signature -> FunName -> TypeName
range sig f = getter _Crange (_typeName._Frange) sig f

arity :: Signature -> FunName -> Int
arity sig f = length (domain sig f)

aDomain :: Signature -> FunName -> [AType]
aDomain sig f = _Fdomain (getFunction sig f)

aRange :: Signature -> FunName -> AType
aRange sig f = _Frange (getFunction sig f)

pfree :: Signature -> FunName -> Term
pfree sig f = _pfree (aRange sig f)

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
