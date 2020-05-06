-- Copyright 2015 Google Inc. All Rights Reserved.
--
-- Licensed under the Apache License, Version 2.0 (the "License");
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

module Examples (flatten, flatten_fail, removePlus0_fail, skolemization) where

flatten = "\
\CONSTRUCTORS\n\
\\n\
\true : Bool\n\
\false : Bool\n\
\\n\
\cons : Expr * List -> List\n\
\nil : List\n\
\\n\
\bool : Bool -> Expr\n\
\list : List -> Expr\n\
\\n\
\FUNCTIONS\n\
\\n\
\flattenE : Expr -> Expr [- cons(list(l1),l2) ]\n\
\flattenL : List -> List [- cons(list(l1),l2) ]\n\
\concat : List * List -> List\n\
\\n\
\RULES\n\
\\n\
\flattenE(bool(b)) -> bool(b)\n\
\flattenE(list(l)) -> list(flattenL(l))\n\
\\n\
\flattenL(cons(bool(b),l)) -> cons(bool(b),flattenL(l))\n\
\flattenL(cons(list(l1),l2)) -> flattenL(concat(l1,l2))\n\
\flattenL(l) -> nil()\n\
\\n\
\concat(cons(e,l1),l2) -> cons(e,concat(l1,l2))\n\
\concat(l1,l2) -> l2"

flatten_fail = "\
\CONSTRUCTORS\n\
\\n\
\true : Bool\n\
\false : Bool\n\
\\n\
\cons : Expr * List -> List\n\
\nil : List\n\
\\n\
\bool : Bool -> Expr\n\
\list : List -> Expr\n\
\\n\
\FUNCTIONS\n\
\\n\
\flattenE : Expr -> Expr [- cons(list(l1),l2) ]\n\
\flattenL : List -> List [- cons(list(l1),l2) ]\n\
\concat : List * List -> List\n\
\\n\
\RULES\n\
\\n\
\flattenE(bool(b)) -> bool(b)\n\
\flattenE(list(l)) -> list(flattenL(l))\n\
\\n\
\flattenL(cons(bool(b),l)) -> cons(bool(b),flattenL(l))\n\
\flattenL(cons(list(l1),l2)) -> concat(flattenL(l1),flattenL(l2))\n\
\flattenL(l) -> nil()\n\
\\n\
\concat(cons(e,l1),l2) -> cons(e,concat(l1,l2))\n\
\concat(l1,l2) -> l2"

removePlus0_fail = "\
\CONSTRUCTORS\n\
\\n\
\z : Int\n\
\s : Int -> Int\n\
\\n\
\int : Int -> Expr\n\
\var : Expr\n\
\\n\
\plus : Expr * Expr -> Expr\n\
\\n\
\FUNCTIONS\n\
\\n\
\removePlus0 : Expr -> Expr [- plus(int(z()),e)]\n\
\\n\
\RULES\n\
\\n\
\removePlus0(int(i)) -> int(i)\n\
\removePlus0(var()) -> var()\n\
\\n\
\removePlus0(plus(int(z),e)) -> removePlus0(e)\n\
\removePlus0(plus(e1,e2)) -> plus(removePlus0(e1),removePlus0(e2))"

skolemization = "\
\CONSTRUCTORS\n\
\\n\
\string : String\n\
\\n\
\predicate : String * Term -> Formula\n\
\and : Formula * Formula -> Formula\n\
\or : Formula * Formula -> Formula\n\
\exists : String * Formula -> Formula\n\
\forall : String * Formula -> Formula\n\
\\n\
\tVar : Var -> Term\n\
\const : String -> Term\n\
\apply : Term * Term -> Term\n\
\concat : Term * Term -> Term\n\
\skolem : String * VarList -> Term\n\
\\n\
\var : String -> Var\n\
\\n\
\varNil : VarList\n\
\varCons : Var * VarList -> VarList\n\
\\n\
\Functions\n\
\\n\
\skolemization : Formula * VarList -> Formula [- exists(s, p) ]\n\
\replaceVarF : Formula * Term -> Formula\n\
\replaceVarT : Term * Term -> Term\n\
\\n\
\RULES\n\
\\n\
\skolemization( predicate(s,t), l ) -> predicate(s,t)\n\
\skolemization( and(p1,p2), l ) -> and( skolemization(p1,l), skolemization(p2,l) )\n\
\skolemization( or(p1,p2), l ) -> or( skolemization(p1,l), skolemization(p2,l) )\n\
\skolemization( exists(s,p), l ) -> skolemization(replaceVarF(p,skolem(s,l)))\n\
\skolemization( forall(s,p), l ) -> forall(s,skolemization(p,varCons(var(s),l)))\n\
\replaceVarF( predicate(s,t), skl ) -> predicate(s, replaceVarT(t,skl))\n\
\replaceVarF( and(p1,p2), skl ) -> and( replaceVarF(p1,skl), replaceVarF(p2,skl) )\n\
\replaceVarF( or(p1,p2), skl ) -> or( replaceVarF(p1,skl), replaceVarF(p2,skl) )\n\
\replaceVarF( exists(s,p), skl ) -> exists(s, replaceVarF(p,skl))\n\
\replaceVarF( forall(s,p), skl ) -> forall(s, replaceVarF(p,skl))\n\
\replaceVarT( tVar(var(s)), skolem(s,l)) -> skolem(s,l)\n\
\replaceVarT( apply(t1,t2), skl ) -> apply( replaceVarT(t1, skl), replaceVarT(t2,skl) )\n\
\replaceVarT( concat (t1,t2), skl ) -> concat( replaceVarT(t1, skl), replaceVarT(t2,skl) )\n\
\replaceVarT( t, skl ) -> t"

