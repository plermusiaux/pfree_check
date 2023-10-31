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
  arity,
  ctorsOfRange,
  ctorsOfSameRange,
  domain,
  inferType,
  isFunc,
  hasType,
  profile,
  typeCheck,
  range
) where

import Datatypes (FunName, TypeName, Constructor(..), Function(..), Signature(..), Term(..), AType(..))
import Data.List ( find )
import Data.Either
import Data.Maybe

import Text.Printf ( printf )

_funName (Constructor f _ _) = f
_Cdomain (Constructor _ d _) = d
_Crange (Constructor _ _ r) = r

_Fdomain (Function _ d _ _) = d
_Frange (Function _ _ r _) = r

getFunction :: Signature -> FunName -> Function
getFunction (Signature _ funs) f = try (find isF funs)
  where try (Just r) = r
        try Nothing = error $ printf "%v is not declared" f
        isF (Function g _ _ _) = f == g

getter :: (Constructor -> a) -> (Function -> a) -> Signature -> FunName -> a
getter getC getF (Signature ctors funs) f = unpack (find isF eithers)
  where unpack (Just r) = either getC getF r
        unpack Nothing = error $ printf "%v is not declared" f
        eithers = (map Left ctors) ++ (map Right funs)
        isF (Left (Constructor g _ _)) = f == g
        isF (Right (Function g  _ _ _)) = f == g

domain :: Signature -> FunName -> [TypeName]
domain = getter _Cdomain _Fdomain

range :: Signature -> FunName -> TypeName
range = getter _Crange _Frange

arity :: Signature -> FunName -> Int
arity sig = length . domain sig

profile :: Signature -> FunName -> [([Term], Term)]
profile sig f = case getFunction sig f of
  Function _ _ _ pr -> pr

ctorsOfRange :: Signature -> TypeName -> [FunName]
ctorsOfRange (Signature ctors _) ty = map _funName (filter hasRangeTy ctors)
  where hasRangeTy (Constructor _ _ ty' ) = ty == ty'

ctorsOfSameRange :: Signature -> FunName -> [FunName]
ctorsOfSameRange sig = ctorsOfRange sig . range sig

isFunc :: Signature -> FunName -> Bool
isFunc (Signature _ funs) f = any isF funs
  where isF (Function g _ _ _) = f==g

hasType :: Signature -> Term -> TypeName -> Bool
hasType sig = (#)
  where
    (Appl f _) # s = range sig f == s
    (Alias _ u) # s = u # s
    Bottom # _ = False
    (AVar _ (AType s1 _)) # s2 = s1 == s2
    (Compl u _) # s = u # s
    (Plus u1 u2) # s = u1 # s || u2 # s

typeCheck :: Signature -> Term -> TypeName -> Term
typeCheck sig = \ t0 s0 -> case (t0 # s0) of
    Nothing      -> t0
    Just (v, s) -> error $ printf "%v does not match expected type %v" v s
  where
    t@(Appl f tl) # s
      | (range sig f /= s)    = Just (t, s)
      | otherwise              = checkArg tl (domain sig f)
      where checkArg [] [] = Nothing
            checkArg (ti:tip) (si:sip) = case ti # si of
              Nothing -> checkArg tip sip
              just    -> just
            checkArg _ _ = Just (t, s)
    (Alias _ u) # s = u # s
    Bottom # s = Just (Bottom, s)
    u@(AVar _ (AType s1 _)) # s2
      | s1 /= s2  = Just (u, s2)
      | otherwise = Nothing
    (Compl u _) # s = u # s
    (Plus u1 u2) # s = maybe (u2 # s) Just (u1 # s)

inferType :: Signature -> Term -> TypeName
inferType sig = typof
  where typof (Appl f _) = range sig f
        typof (AVar _ (AType s _)) = s
        typof (Alias _ u) = typof u
        typof (Compl u _) = typof u
