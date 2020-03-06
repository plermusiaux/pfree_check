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

module Datatypes (
  FunName(..),
  TypeName(..),
  VarName(..),
  Constructor(..),
  Function(..),
  Signature(..),
  Term(..),
  AType(..),
  Rule(..),
  Module(..)
) where

import Data.List ( intercalate )
import Data.Maybe ( fromJust )
import Data.String ( IsString(..) )

{- Datatypes -}

newtype VarName = VarName String
  deriving (Eq, Ord)

newtype FunName = FunName String
  deriving (Eq, Ord)

newtype TypeName = TypeName String
  deriving (Eq, Ord)

data AType = AType TypeName Term
  deriving (Eq, Ord)

data Constructor = Constructor FunName [TypeName] TypeName
  deriving (Eq, Ord)

data Function = Function FunName [AType] AType
  deriving (Eq, Ord)

data Signature = Signature [Constructor] [Function]
  deriving (Eq, Ord)

data Term = Appl FunName [Term]
          | Var VarName -- Term TypeName
          | Plus Term Term
          | Compl Term Term
          | Alias VarName Term
          | Anti Term
          | Bottom
          | AVar VarName AType
  deriving (Eq, Ord)

data Rule = Rule Term Term
  deriving (Eq, Ord)

data Module = Module Signature [Rule]
  deriving (Eq, Ord, Show)

{- Pretty Printing -}

instance Show VarName where
  show (VarName x) = x

instance Show FunName where
  show (FunName x) = x

instance Show TypeName where
  show (TypeName ty) = ty

instance Show AType where
  show (AType s Bottom) = show s
  show (AType s p) = show s ++ "[-" ++ show p ++ "]"

parSep :: [String] -> String
parSep ss = "(" ++ intercalate ", " ss ++ ")"

instance Show Constructor where
  show (Constructor f tys ty) = show f ++ ": " ++ intercalate " * " (map show tys) ++ " -> " ++ show ty

instance Show Function where
  show (Function f d r) = show f ++ ": " ++ intercalate " * " (map show d) ++ " -> " ++ show r

instance Show Signature where
  show (Signature ctors funs) = show (ctors, funs)

instance Show Term where
  show (Appl f ps) = show f ++ parSep (map show ps)
  show (Var x) = show x -- ++ " : " ++ show s ++ "[-" ++ show p ++ "]"
  show (Plus p1 p2) = "(" ++ show p1 ++ " + " ++ show p2 ++ ")"
  show (Compl p1 p2) = "(" ++ show p1 ++ " \\ " ++ show p2 ++ ")"
  show (Alias x p) = show x ++ "@" ++ show p
  show (Anti p) = "!" ++ show p
  show Bottom = "⊥"
  show (AVar x s) = show x ++ " : " ++ show s

instance Show Rule where
  show (Rule lhs rhs) = show lhs ++ " -> " ++ show rhs

{- IsString instances -}

instance IsString VarName where
  fromString = VarName

instance IsString FunName where
  fromString = FunName

instance IsString TypeName where
  fromString = TypeName

