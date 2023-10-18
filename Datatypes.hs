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

import Text.Printf

{- Datatypes -}

data VarName = VarName String
             | NoName
  deriving (Eq, Ord)

newtype FunName = FunName String
  deriving (Eq, Ord)

newtype TypeName = TypeName String
  deriving (Eq, Ord)

data AType = AType TypeName Term
           | Unknown
  deriving (Eq, Ord)

data Term = Appl FunName [Term]
          | Plus Term Term
          | Compl Term Term
          | Alias VarName Term
          | Anti Term
          | Bottom
          | AVar VarName AType
  deriving (Eq, Ord)

data Rule = Rule Term Term
  deriving (Eq, Ord)

data Constructor = Constructor FunName [TypeName] TypeName

data Function = Function FunName [TypeName] TypeName [([Term], Term)]

data Signature = Signature [Constructor] [Function]

data Module = Module Signature [Rule]

{- Pretty Printing -}

type FormatA a = (a -> FieldFormatter, a)

instance PrintfArg (FormatA a) where
  formatArg (f, x) fmt | fmtChar fmt == 'a' = f x (fmt { fmtChar = 'v' })
  formatArg _ fmt = errorBadFormat $ fmtChar fmt

formatList :: (a -> FieldFormatter) -> String -> [a] -> FormatA [a]
formatList f sep = (format,)
  where format [] fmt = id
        format [x] fmt = f x fmt
        format (x:xs) fmt = printf "%a%s%a%s" (f, x) sep (format, xs)

instance PrintfArg VarName where
  formatArg x fmt | fmtChar fmt == 'v' =
    case x of
      VarName s -> formatString s fmt
      NoName    -> formatString "_" fmt
  formatArg _ fmt = errorBadFormat $ fmtChar fmt

instance Show VarName where
  show = printf "%v"

instance PrintfArg FunName where
  formatArg (FunName name) fmt
    | fmtChar fmt == 'v' = formatString name fmt
  formatArg _ fmt = errorBadFormat $ fmtChar fmt

instance Show FunName where
  show (FunName name) = name

instance PrintfArg TypeName where
  formatArg (TypeName ty) fmt
    | fmtChar fmt == 'v' = formatString ty fmt
  formatArg _ fmt = errorBadFormat $ fmtChar fmt

instance Show TypeName where
  show (TypeName ty) = ty

instance PrintfArg AType where
  formatArg ty fmt | fmtChar fmt == 'v' =
    case ty of
      AType s Bottom -> formatArg s fmt
      AType s p      -> printf "%v[-%v]%s" s p
      Unknown        -> id
  formatArg _ fmt = errorBadFormat $ fmtChar fmt

instance Show AType where
  show = printf "%v"

instance PrintfArg Constructor where
  formatArg (Constructor f tys ty) fmt | fmtChar fmt == 'v' =
    printf "%v: %v -> %a%s" f (formatList formatArg " * " tys) ty
  formatArg _ fmt = errorBadFormat $ fmtChar fmt

instance Show Constructor where
  show = printf "%v"

instance PrintfArg Function where
  formatArg (Function f d r pr) fmt | fmtChar fmt == 'v' =
    printf "%v: %a%s" f (formatList profile " | " pr)
    where profile (qs, p) _ = printf "%a -> %v%s" (formatList formatArg " * " qs) p
  formatArg _ fmt = errorBadFormat $ fmtChar fmt

instance Show Function where
  show = printf "%v"

instance Show Signature where
  show (Signature ctors funs) = show (ctors, funs)

instance PrintfArg Term where
  formatArg t fmt | fmtChar fmt == 'v' =
    case t of
      Appl f ps      -> printf "%v(%a)%s" f (formatList formatArg ", " ps)
      Plus p1 p2     -> printf "(%v + %v)%s" p1 p2
      Compl p1 p2    -> printf "(%v \\ %v)%s" p1 p2
      Alias x p      -> printf "%v@%v%s" x p
      Anti p         -> printf "!%v%s" p
      Bottom         -> formatChar '⊥' fmt
      AVar x Unknown -> formatArg x fmt
      AVar x s       -> printf "%v : %v%s" x s
  formatArg _ fmt = errorBadFormat $ fmtChar fmt

instance Show Term where
  show = printf "%v"

instance PrintfArg Rule where
  formatArg (Rule lhs rhs) fmt | fmtChar fmt == 'v' =
    printf "%v -> %v%s" lhs rhs
  formatArg _ fmt = errorBadFormat $ fmtChar fmt

instance Show Rule where
  show = printf "%v"

{- IsString instances -}

instance IsString VarName where
  fromString = VarName

instance IsString FunName where
  fromString = FunName

instance IsString TypeName where
  fromString = TypeName

