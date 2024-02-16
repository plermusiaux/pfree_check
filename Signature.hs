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
  hasType,
  inferType,
  isFunc,
  profile,
  range,
  sigOf,
  typeCheck
) where

import Datatypes (FunName, TypeName, VarName(..), Constructor(..), Function(..), Signature(..), Term(..), AType(..))
import Data.List ( find )
import Data.Either
import Data.Maybe

import Text.Printf ( printf )

_funName (Constructor f _ _) = f
_Cdomain (Constructor _ d _) = d
_Crange (Constructor _ _ r) = r
_CsigOf (Constructor _ d r) = (d, r)

_Fdomain (Function _ d _ _) = d
_Frange (Function _ _ r _) = r
_FsigOf (Function _ d r _) = (d, r)

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

sigOf :: Signature -> FunName -> ([TypeName], TypeName)
sigOf = getter _CsigOf _FsigOf

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

inferType :: Signature -> Term -> TypeName
inferType sig = typof
  where typof (Appl f tl) =
          if checkArg tl d then s
          else error $ printf "symbol [%v] expects %i arguments" f (length d)
          where (d, s) = sigOf sig f
        typof (AVar _ (AType s _)) = s
        typof (Alias _ u) = typof u
        typof (Plus u1 u2) =
          let s1 = typof u1 in
          if s1 == typof u2 then s1
          else error $ printf "type of %v does not match type of %v" u1 u2
        typof (Compl u r) =
          let s = typof u in
          if s == typof r then s
          else error $ printf "type of %v does not match type of %v" u r
        typof Bottom = error $ printf "cannot infer type of ⊥"
        checkArg [] [] = True
        checkArg (t:tl) (s:sl) = let !_ = typeCheck sig t s in checkArg tl sl
        checkArg _ _ = False

typeCheck :: Signature -> Term -> TypeName -> Term
typeCheck sig = (#)
  where (Appl f tl) # s =
          case checkArg tl d of
            Just ul
              | s == s'   -> Appl f ul
              | otherwise -> error $ printf "return type of [%v] does not match expected type %v" f s
            _             -> error $ printf "symbol [%v] expects %i arguments" f (length d)
          where (d, s') = sigOf sig f
        (AVar x Unknown) # s = AVar x (AType s Bottom)
        t@(AVar x (AType s1 _)) # s2 =
          if s1 == s2 then t
          else error $ printf "variable %v is typed %v, which does not match expected type %v" x s1 s2
        Bottom # s = error $ printf "type of ⊥ is undefined"
        (Alias x u) # s = Alias x $! (u # s)
        (Plus u1 u2) # s =
          (Plus $! (u1 # s)) $! (u2 # s)
        (Compl u r) # s =
          (Compl $! (u # s)) $! (r # s)
        (Anti p) # s = Compl (AVar NoName (AType s Bottom)) $! (p # s)
        checkArg [] [] = Just []
        checkArg (t:tl) (s:sl) = case checkArg tl sl of
          Just ul -> Just $! (t # s) : ul
          nothing -> nothing
        checkArg _ _ = Nothing

