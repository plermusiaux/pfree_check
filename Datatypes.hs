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
{-# LANGUAGE DeriveGeneric, DeriveAnyClass #-}

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

import GHC.Generics (Generic)
import Control.DeepSeq

{- Datatypes -}

data VarName = VarName String
             | NoName
  deriving (Eq, Ord, Generic, NFData)

newtype FunName = FunName String
  deriving (Eq, Ord, Generic, NFData)

newtype TypeName = TypeName String
  deriving (Eq, Ord, Generic, NFData)

data AType = AType TypeName Term
           | Unknown
  deriving (Eq, Ord, Generic, NFData)

data Term = Appl FunName [Term]
          | Plus Term Term
          | Compl Term Term
          | Alias VarName Term
          | Anti Term
          | Bottom
          | AVar VarName AType
  deriving (Eq, Ord, Generic, NFData)

data Rule = Rule Term Term
  deriving (Eq, Ord, Generic, NFData)

data Constructor = Constructor FunName [TypeName] TypeName
  deriving (Generic, NFData)

data Function = Function FunName [TypeName] TypeName [([Term], Term)]
  deriving (Generic, NFData)

data Signature = Signature [Constructor] [Function]
  deriving (Generic, NFData)

data Module = Module Signature [Rule]
  deriving (Generic, NFData)

{- Pretty Printing -}

instance Show VarName where
  show (VarName x) = x
  show NoName = "_"

instance Show FunName where
  show (FunName x) = x

instance Show TypeName where
  show (TypeName ty) = ty

instance Show AType where
  show (AType s Bottom) = show s
  show (AType s p) = show s ++ "[-" ++ show p ++ "]"
  show Unknown = []

parSep :: [String] -> String
parSep ss = "(" ++ intercalate ", " ss ++ ")"

instance Show Constructor where
  show (Constructor f tys ty) = show f ++ ": " ++ intercalate " * " (map show tys) ++ " -> " ++ show ty

instance Show Function where
  show (Function f d r pr) = show f ++ ": " ++ intercalate " | " profiles
    where profiles = map showProfile pr
          showProfile (qs, p) = intercalate " * " (map show (zipWith AType d qs)) ++ " -> " ++ show (AType r p)

instance Show Signature where
  show (Signature ctors funs) = show (ctors, funs)

instance Show Term where
  show (Appl f ps) = show f ++ parSep (map show ps)
  show (Plus p1 p2) = "(" ++ show p1 ++ " + " ++ show p2 ++ ")"
  show (Compl p1 p2) = "(" ++ show p1 ++ " \\ " ++ show p2 ++ ")"
  show (Alias x p) = show x ++ "@" ++ show p
  show (Anti p) = "!" ++ show p
  show Bottom = "⊥"
  show (AVar x s) = case s of
    Unknown -> show x
    _       -> show x ++ " : " ++ show s


instance Show Rule where
  show (Rule lhs rhs) = show lhs ++ " -> " ++ show rhs

{- IsString instances -}

instance IsString VarName where
  fromString = VarName

instance IsString FunName where
  fromString = FunName

instance IsString TypeName where
  fromString = TypeName

