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


module Parser (parseModule) where

import Datatypes
import Text.Parsec
import Text.Parsec.String
import Text.Parsec.Language
import qualified Text.Parsec.Token as P

language = javaStyle
  { P.reservedNames = ["CONSTRUCTORS", "FUNCTIONS", "RULES"]
  , P.reservedOpNames = ["=", "->", ":", "*", "!", "+", "\\", "-"]
  }

lexer = P.makeTokenParser javaStyle

parens = P.parens lexer
identifier = P.identifier lexer
colon = P.colon lexer
comma = P.comma lexer
lexeme = P.lexeme lexer
whiteSpace = P.whiteSpace lexer
brackets = P.brackets lexer

equals = P.reservedOp lexer "="
arrow = P.reservedOp lexer "->"
pipe = P.reservedOp lexer "|"
star = P.reservedOp lexer "*"
bang = P.reservedOp lexer "!"
plus = P.reservedOp lexer "+"
minus = P.reservedOp lexer "\\"
mfree = P.reservedOp lexer "-"

constructorsKw = P.reserved lexer "CONSTRUCTORS"
functionsKw = P.reserved lexer "FUNCTIONS"
rulesKw = P.reserved lexer "RULES"

funName = FunName <$> identifier
varName = VarName <$> identifier
typeName = TypeName <$> identifier

termSum :: Parser Term
termSum = mkPlus <$> termCompl `sepBy1` plus
  where mkPlus [t] = t
        mkPlus ts = foldr1 Plus ts

termCompl :: Parser Term
termCompl = try (mkCompl <$> term <*> (minus >> term))
            <|> term
  where mkCompl t1 t2 = Compl t1 t2

term :: Parser Term
term = try (Appl <$> funName <*> parens (termSum `sepBy` comma))
       <|> Anti <$> (bang >> term)
       <|> mkVar <$> varName
       <|> parens termSum
  where mkVar name = AVar name Unknown

rule :: Parser Rule
rule = mkRule <$> termSum <*> arrow <*> term
  where mkRule lhs _ rhs = Rule lhs rhs

rules :: Parser [Rule]
rules = many rule

funProfile :: Parser ([TypeName], TypeName, [([Term], Term)])
funProfile = mkProfile <$> (funType `sepBy1` pipe)
  where
    mkProfile ((d, qs, (r, p)):l) = foldl buildProfile (d, r, [(qs, p)]) l
    buildProfile (d, r, l) (d', qs, (r', p))
      | d' == d && r' == r = (d, r, (qs, p):l)
      | otherwise          = error "inconsistant function profile"

funType :: Parser ([TypeName], [Term], (TypeName, Term))
funType = try (mkFType <$> (aType `sepBy1` star) <*> (arrow >> aType))
          <|> mkEmptyType <$> aType
  where
    mkFType domain range = (d, qs, range)
      where (d, qs) = unzip domain
    mkEmptyType range = ([], [], range)

aType :: Parser (TypeName, Term)
aType = try (mkAType <$> typeName <*> (brackets (mfree >> term)))
        <|> mkDefaultAType <$> typeName
  where mkDefaultAType s = (s, Bottom)
        mkAType s p = (s, p)

consType :: Parser ([TypeName], TypeName)
consType = try (mkFType <$> (typeName `sepBy` star) <*> (arrow >> typeName))
          <|> mkEmptyType <$> typeName
  where
    mkFType domain range = (domain, range)
    mkEmptyType range = ([], range)

constructor :: Parser Constructor
constructor = mkDecl <$> funName <*> (colon >> consType)
  where mkDecl f (domain, range) = Constructor f domain range

constructors :: Parser [Constructor]
constructors = many (try constructor)

function :: Parser Function
function = mkDecl <$> funName <*> (colon >> funProfile)
  where mkDecl f (domain, range, profile) = Function f domain range profile

functions :: Parser [Function]
functions = many (try function)

modul :: Parser Module
modul = mkModule <$> (constructorsKw >> constructors) <*> (functionsKw >> functions) <*> (rulesKw >> rules)
  where mkModule ctors funs rules = Module (Signature ctors funs) rules

parseModule :: String -> String -> Either ParseError Module
parseModule sourceName input = parse (whiteSpace *> modul <* eof) sourceName input
