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

module Examples (flatten1, flatten_fail, flatten2, flatten3, negativeNF,
                 skolemization, removePlus0_fail, removePlus0, multiply0,
                 non_linear, insertionSort, mergeSort, Examples.reverse,
                 reverseTwice, delete, sortedDelete, otrs) where

flatten1 = "\
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

flatten2 = "\
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
\concat : List [- cons(list(l1),l2) ] * List [- cons(list(l1),l2) ] -> List [- cons(list(l1),l2) ]\n\
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

flatten3 = "\
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
\fconcat : List * List -> List [- cons(list(l1),l2) ]\n\
\\n\
\Rules\n\
\\n\
\flattenE(bool(b)) -> bool(b)\n\
\flattenE(list(l)) -> list(flattenL(l))\n\
\\n\
\flattenL(cons(list(l1), l2)) -> fconcat(l1, l2)\n\
\flattenL(cons(bool(b), l)) -> cons(bool(b), flattenL(l))\n\
\flattenL(nil()) -> nil()\n\
\\n\
\fconcat(cons(bool(b), l1), l2) -> cons(bool(b), fconcat(l1,l2))\n\
\fconcat(cons(list(l1), l2), l3) -> fconcat(l1, cons(list(l2),l3))\n\
\fconcat(nil(), l) -> flattenL(l)"

lopstr = "\
\CONSTRUCTORS\n\
\\n\
\c1 : s2 * s1 -> s1\n\
\c2 : s3 -> s1\n\
\\n\
\c3 : s1 -> s2\n\
\c4 : s3 -> s2\n\
\\n\
\c5 : s3 -> s3\n\
\c6 : s3\n\
\\n\
\FUNCTIONS\n\
\\n\
\f : s1 -> s1 [- c1(c4(x), y) ]\n\
\g : s2 -> s2 [- c4(x) ]\n\
\\n\
\RULES\n\
\\n\
\f(c1(x,y)) -> c1(g(x), f(y))\n\
\f(c2(z)) -> c2(z)\n\
\g(c3(y)) -> c3(f(y))\n\
\g(c4(z)) -> c3(c2(z))"

negativeNF = "\
\CONSTRUCTORS\n\
\\n\
\string : String\n\
\\n\
\not : Formula -> Formula\n\
\predicate : String * Term -> Formula\n\
\and : Formula * Formula -> Formula\n\
\or : Formula * Formula -> Formula\n\
\impl : Formula * Formula -> Formula\n\
\exists : String * Formula -> Formula\n\
\forall : String * Formula -> Formula\n\
\\n\
\tVar : Var -> Term\n\
\const : String -> Term\n\
\apply : Term * Term -> Term\n\
\concat : Term * Term -> Term\n\
\\n\
\var : String -> Var\n\
\\n\
\varNil : VarList\n\
\varCons : Var * VarList -> VarList\n\
\\n\
\Functions\n\
\\n\
\// nnf : Formula -> Formula [- (impl(p1,p2) + not(and(p1,p2)) + not(or(p1,p2)) + not(forall(s,p)) + not(exists(s,p)) + not(not(p))) ]\n\
\nnf : Formula -> Formula [- (impl(p1,p2) + not(!predicate(s))) ]\n\
\\n\
\RULES\n\
\\n\
\nnf(predicate(s,t)) -> predicate(s,t)\n\
\nnf(not(predicate(s,t))) -> not(predicate(s,t))\n\
\nnf(not(and(p1, p2))) -> or(nnf(not(p1)), nnf(not(p2)))\n\
\nnf(not(or(p1, p2))) -> and(nnf(not(p1)), nnf(not(p2)))\n\
\nnf(not(exists(s, p))) -> forall(s, nnf(not(p)))\n\
\nnf(not(forall(s, p))) -> exists(s, nnf(not(p)))\n\
\nnf(not(impl(p1, p2))) -> and(nnf(p1), nnf(not(p2)))\n\
\nnf(not(not(p))) -> nnf(p)\n\
\nnf(impl(p1, p2)) -> or(nnf(not(p1)), nnf(p2))\n\
\nnf(and(p1, p2)) -> and(nnf(p1), nnf(p2))\n\
\nnf(or(p1, p2)) -> or(nnf(p1), nnf(p2))\n\
\nnf(exists(s, p)) -> exists(s, nnf(p))\n\
\nnf(forall(s, p)) -> forall(s, nnf(p))"

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
\skolemization( exists(s,p), l ) -> skolemization(replaceVarF(p,skolem(s,l)), l)\n\
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

removePlus0 ="\
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
\plusCheck : Expr [- plus(int(z()),e)] * Expr [- plus(int(z()),e)] -> Expr [- plus(int(z()),e)]\n\
\\n\
\RULES\n\
\\n\
\removePlus0(int(i)) -> int(i)\n\
\removePlus0(var()) -> var()\n\
\\n\
\removePlus0(plus(int(z),e)) -> removePlus0(e)\n\
\removePlus0(plus(e1,e2)) -> plusCheck(removePlus0(e1),removePlus0(e2))\n\
\\n\
\plusCheck(int(z()), e) -> e\n\
\plusCheck(e, int(z())) -> e\n\
\plusCheck(e1\\int(z), e2\\int(z)) -> plus(e1, e2)"

multiply0 = "\
\CONSTRUCTORS\n\
\\n\
\z : Int\n\
\s : Int -> Int\n\
\\n\
\FUNCTIONS\n\
\\n\
\plus : Int [- s(i)] * Int [- s(i)] -> Int [- s(i)]\n\
\\n\
\mult : Int [- s(i)] * Int -> Int [- s(i)]\n\
\     | Int * Int [- s(i)] -> Int [- s(i)]\n\
\\n\
\RULES\n\
\\n\
\plus(z(), y) -> y\n\
\plus(s(x), y) -> plus(x, s(y))\n\
\\n\
\mult(z(), y) -> z()\n\
\mult(s(x), y) -> plus(y, mult(x, y))"

non_linear="\
\CONSTRUCTORS\n\
\\n\
\c : S2 * S2 -> S1\n\
\d : S1 * S1 -> S1\n\
\\n\
\a : S2\n\
\b : S2\n\
\\n\
\e : S1\n\
\\n\
\FUNCTIONS\n\
\\n\
\f : S1 -> S1 [- c(a(), b()) ]\n\
\g : S1 -> S2\n\
\\n\
\RULES\n\
\\n\
\f(c(x, y)) -> c(x, x)\n\
\f(d(x, y)) -> c(g(x), g(x))\n\
\f(e()) -> e()"

insertionSort = "\
\CONSTRUCTORS\n\
\\n\
\true : Bool\n\
\false : Bool\n\
\\n\
\A : Value\n\
\B : Value\n\
\\n\
\cons : Value * List -> List\n\
\nil : List\n\
\\n\
\FUNCTIONS\n\
\\n\
\leq : Value * Value [- A()] -> Bool [- false()]\n\
\    | Value [- B()] * Value -> Bool [- false()]\n\
\    | Value [- A()] * Value [- B()] -> Bool [- true()]\n\
\\n\
\ite : Bool [- true()] * List * List [- cons(B(), cons(A(), l))] -> List [- cons(B(), cons(A(), l))]\n\
\    | Bool [- false()] * List [- cons(B(), cons(A(), l))] * List -> List [- cons(B(), cons(A(), l))]\n\
\//    | Bool * List [- cons(B(), cons(A(), l))] * List [- cons(B(), cons(A(), l))] -> List [- cons(B(), cons(A(), l))]\n\
\\n\
\insert : Value * List [- cons(B(), cons(A(), l))] -> List [- cons(B(), cons(A(), l))]\n\
\\n\
\sort : List -> List [- cons(B(), cons(A(), l))]\n\
\\n\
\RULES\n\
\\n\
\leq(x, B()) -> true()\n\
\leq(A(), y) -> true()\n\
\leq(B(), A()) -> false()\n\
\\n\
\ite(true(), l1, l2) -> l1\n\
\ite(false(), l1, l2) -> l2\n\
\\n\
\insert(x, nil()) -> cons(x, nil())\n\
\insert(x, cons(y, l)) -> ite(leq(x,y), cons(x, cons(y, l)), cons(y, insert(x, l)))\n\
\// to pass in linear or strict mode, replace last rule with:\n\
\//insert(x@(A()+B()), cons(y@(A()+B()), l)) -> ite(leq(x,y), cons(x, cons(y, l)), cons(y, insert(x, l)))\n\
\\n\
\sort(cons(x, l)) -> insert(x, sort(l))\n\
\sort(nil()) -> nil()"

mergeSort = "\
\CONSTRUCTORS\n\
\\n\
\true : Bool\n\
\false : Bool\n\
\\n\
\A : Value\n\
\B : Value\n\
\\n\
\cons : Value * List -> List\n\
\nil : List\n\
\\n\
\pair : List * List -> Pair\n\
\\n\
\FUNCTIONS\n\
\\n\
\leq : Value * Value [- A()] -> Bool [- false()]\n\
\    | Value [- B()] * Value -> Bool [- false()]\n\
\    | Value [- A()] * Value [- B()] -> Bool [- true()]\n\
\\n\
\ite : Bool [- true()] * List * List [- cons(B(), cons(A(), l))] -> List [- cons(B(), cons(A(), l))]\n\
\    | Bool [- false()] * List [- cons(B(), cons(A(), l))] * List -> List [- cons(B(), cons(A(), l))]\n\
\    | Bool [- true()] * List * List [- cons(A(), l)] -> List [- cons(A(), l)]\n\
\    | Bool [- false()] * List [- cons(A(), l)] * List -> List [- cons(A(), l)]\n\
\\n\
\split : List * List * List -> Pair\n\
\\n\
\mergeP : Pair [- cons(B(), cons(A(), l))] -> List [- cons(B(), cons(A(), l))]\n\
\       | Pair [- cons(A(), l)] -> List [- cons(A(), l)]\n\
\\n\
\sort : List -> List [- cons(B(), cons(A(), l))]\n\
\sortP : Pair -> Pair [- cons(B(), cons(A(), l))]\n\
\\n\
\RULES\n\
\\n\
\leq(x, B()) -> true()\n\
\leq(A(), y) -> true()\n\
\leq(B(), A()) -> false()\n\
\\n\
\ite(true(), l1, l2) -> l1\n\
\ite(false(), l1, l2) -> l2\n\
\\n\
\split(nil(), l1, l2) -> pair(l1, l2)\n\
\split(cons(x, nil()), l1, l2) -> pair(cons(x, l1), l2)\n\
\split(cons(x, cons(y, l)), l1, l2) -> split(l, cons(x, l1), cons(y,l2))\n\
\\n\
\mergeP(pair(nil(), l)) -> l\n\
\mergeP(pair(l, nil())) -> l\n\
\mergeP(pair(cons(x, l1), cons(y, l2))) -> ite(leq(x, y), cons(x, mergeP(pair(l1, cons(y, l2)))), cons(y, mergeP(pair(cons(x, l1), l2))))\n\
\// to pass in linear or strict mode, replace last rule with:\n\
\//mergeP(pair(cons(x@(A()+B()), l1), cons(y@(A()+B()), l2))) -> ite(leq(x, y), cons(x, mergeP(pair(l1, cons(y, l2)))), cons(y, mergeP(pair(cons(x, l1), l2))))\n\
\\n\
\sort(nil()) -> nil()\n\
\sort(cons(x, nil())) -> cons(x, nil())\n\
\sort(cons(x, cons(y, l))) -> mergeP(sortP(split(cons(x, cons(y, l)), nil(), nil())))\n\
\\n\
\sortP(pair(l1, l2)) -> pair(sort(l1), sort(l2))"

reverse = "\
\CONSTRUCTORS\n\
\\n\
\A : Value\n\
\B : Value\n\
\\n\
\cons : Value * List -> List\n\
\nil : List\n\
\\n\
\FUNCTIONS\n\
\\n\
\rev : List [- cons(B(), cons(A(), l))] -> List [- cons(A(), cons(B(), l))]\n\
\\n\
\reverse : List [- cons(B(), cons(A(), l))] * List [- cons(B(), l)] -> List [- cons(A(), cons(B(), l))]\n\
\        | List [- cons(A(),l)] * List [- cons(A(), cons(B(), l))] -> List [- cons(A(), cons(B(), l))]\n\
\\n\
\RULES\n\
\\n\
\reverse(nil(), l) -> l\n\
\reverse(cons(v, l1), l2) -> reverse(l1, cons(v, l2))\n\
\\n\
\rev(l) -> reverse(l, nil())"

reverseTwice = "\
\CONSTRUCTORS\n\
\\n\
\A : Value\n\
\B : Value\n\
\\n\
\cons : Value * List -> List\n\
\nil : List\n\
\\n\
\FUNCTIONS\n\
\\n\
\revRev : List [- cons(B(), cons(A(), l))] -> List [- cons(B(), cons(A(), l))]\n\
\\n\
\reverse : List [- cons(B(), cons(A(), l))] * List [- cons(B(), l)] -> List [- cons(A(), cons(B(), l))]\n\
\        | List [- cons(A(),l)] * List [- cons(A(), cons(B(), l))] -> List [- cons(A(), cons(B(), l))]\n\
\        | List [- cons(A(), cons(B(), l))] * List [- cons(A(), l)] -> List [- cons(B(), cons(A(), l))]\n\
\        | List [- cons(B(),l)] * List [- cons(B(), cons(A(), l))] -> List [- cons(B(), cons(A(), l))]\n\
\\n\
\RULES\n\
\\n\
\reverse(nil(), l) -> l\n\
\reverse(cons(v, l1), l2) -> reverse(l1, cons(v, l2))\n\
\\n\
\revRev(l) -> reverse(reverse(l, nil()), nil())"

delete = "\
\CONSTRUCTORS\n\
\\n\
\true : Bool\n\
\false : Bool\n\
\\n\
\A : Value\n\
\B : Value\n\
\\n\
\cons : Value * List -> List\n\
\nil : List\n\
\\n\
\FUNCTIONS\n\
\\n\
\eq : Value [- A()] * Value [- A()] -> Bool [- false()]\n\
\   | Value [- B()] * Value [- B()] -> Bool [- false()]\n\
\   | Value [- A()] * Value [- B()] -> Bool [- true()]\n\
\   | Value [- B()] * Value [- A()] -> Bool [- true()]\n\
\\n\
\delete : Value [- A()] * List -> List [- cons(B(), l)]\n\
\       | Value [- B()] * List -> List [- cons(A(), l)]\n\
\\n\
\ite : Bool [- false()] * List [- cons(A(), l)] * List -> List [- cons(A(), l)]\n\
\    | Bool [- false()] * List [- cons(B(), l)] * List -> List [- cons(B(), l)]\n\
\    | Bool [- true()] * List * List [- cons(A(), l)] -> List [- cons(A(), l)]\n\
\    | Bool [- true()] * List * List [- cons(B(), l)] -> List [- cons(B(), l)]\n\
\\n\
\RULES\n\
\\n\
\delete(x, cons(y, l)) -> ite(eq(x, y), delete(x, l), cons(y, delete(x, l)))\n\
\// to pass in linear or strict mode, replace last rule with:\n\
\//delete(x, cons(y@(A()+B()), l)) -> ite(eq(x, y), delete(x, l), cons(y, delete(x, l)))\n\
\delete(v, nil()) -> nil()\n\
\\n\
\ite(true(), l1, l2) -> l1\n\
\ite(false(), l1, l2) -> l2"

sortedDelete = "\
\CONSTRUCTORS\n\
\\n\
\true : Bool\n\
\false : Bool\n\
\\n\
\A : Value\n\
\B : Value\n\
\\n\
\cons : Value * List -> List\n\
\nil : List\n\
\\n\
\FUNCTIONS\n\
\\n\
\eq : Value [- A()] * Value [- A()] -> Bool [- false()]\n\
\   | Value [- B()] * Value [- B()] -> Bool [- false()]\n\
\   | Value [- A()] * Value [- B()] -> Bool [- true()]\n\
\   | Value [- B()] * Value [- A()] -> Bool [- true()]\n\
\\n\
\delete : Value * List [- cons(B(), cons(A(), l))] -> List [- cons(B(), cons(A(), l))]\n\
\       | Value * List [- cons(A(), l)] -> List [- cons(A(), l)]\n\
\\n\
\ite : Bool [- false()] * List [- cons(B(), cons(A(), l))] * List -> List [- cons(B(), cons(A(), l))]\n\
\    | Bool [- true()] * List * List [- cons(B(), cons(A(), l))] -> List [- cons(B(), cons(A(), l))]\n\
\    | Bool [- false()] * List [- cons(A(), l)] * List -> List [- cons(A(), l)]\n\
\    | Bool [- true()] * List * List [- cons(A(), l)] -> List [- cons(A(), l)]\n\
\\n\
\RULES\n\
\\n\
\delete(x, cons(y, l)) -> ite(eq(x, y), l, cons(y, delete(x, l)))\n\
\// to pass in linear or strict mode, replace last rule with:\n\
\//delete(x@(A() + B()), cons(y@(A() + B()), l)) -> ite(eq(x, y), l, cons(y, delete(x, l)))\n\
\delete(v, nil()) -> nil()\n\
\\n\
\ite(true(), l1, l2) -> l1\n\
\ite(false(), l1, l2) -> l2"

otrs = "\
\CONSTRUCTORS\n\
\\n\
\name : Nat -> Name\n\
\\n\
\sig : Name * Nat * Signature -> Signature\n\
\empty : Signature\n\
\\n\
\nil : TermList\n\
\cons : Term * TermList -> TermList\n\
\\n\
\bot : Term\n\
\var : Name -> Term\n\
\appl : Name * TermList -> Term\n\
\plus : Term * Term -> Term\n\
\\n\
\z : Nat\n\
\s : Nat -> Nat\n\
\\n\
\true : Bool\n\
\false : Bool\n\
\\n\
\FUNCTIONS\n\
\\n\
\eq : Nat * Nat -> Bool\n\
\\n\
\ite : Bool * Term [- cons(bot(),tl) ] * Term [- cons(bot(),tl) ] -> Term [- cons(bot(),tl) ]\n\
\    | Bool * Term [- plus(bot(),v) ] * Term [- plus(bot(),v) ] -> Term [- plus(bot(),v) ]\n\
\    | Bool * Term [- plus(u,bot()) ] * Term [- plus(u,bot()) ] -> Term [- plus(u,bot()) ]\n\
\    | Bool * Term [- cons(plus(t1,t2),tl) ] * Term [- cons(plus(t1,t2),tl) ] -> Term [- cons(plus(t1,t2),tl) ]\n\
\\n\
\add : Term [- cons(bot(),tl) ] * Term [- cons(bot(),tl) ] -> Term [- cons(bot(),tl) ]\n\
\    | Term [- plus(bot(),v) ] * Term [- plus(bot(),v) ] -> Term [- plus(bot(),v) ]\n\
\    | Term [- plus(u,bot()) ] * Term [- plus(u,bot()) ] -> Term [- plus(u,bot()) ]\n\
\    | Term [- cons(plus(t1,t2), tl) ] * Term [- cons(plus(t1,t2), tl) ] -> Term [- cons(plus(t1,t2), tl) ]\n\
\\n\
\complement : Signature * Term * Term -> Term [- ( cons(bot()+plus(t1,t2),tl) + plus(bot(),v) + plus(u,bot()) ) ]\n\
\\n\
\generate : Signature -> Term [- ( cons(bot(),tl) + plus(bot(),v) + plus(u,bot()) ) ]\n\
\build : Name * Nat * TermList [- bot() ] -> Term [- bot() ]\n\
\\n\
\interleave : Name * TermList * TermList * TermList * Signature -> Term [- ( cons(bot()+plus(t1,t2),tl) + plus(bot(),v) + plus(u,bot()) ) ]\n\
\\n\
\collectPlus : Term -> Term [- ( cons(bot()+plus(t1,t2),tl) + plus(bot(),v) + plus(u,bot()) ) ]\n\
\\n\
\split : Name * Term [- ( cons(bot(),tl) + plus(bot(),v) + plus(u,bot()) ) ] * TermList * TermList [- bot() ]  -> Term [- ( cons(bot(),tl) + plus(bot(),v) + plus(u,bot()) ) ]\n\
\      | Name * Term [-  cons(plus(t1,t2),tl) ] * TermList * TermList [- plus(t1,t2) ]  -> Term [- cons(plus(t1,t2),tl) ]\n\
\reverse : TermList [- bot() ] * TermList [- bot() ] -> TermList [- bot() ]\n\
\        | TermList [- plus(t1,t2) ] * TermList [- plus(t1,t2) ] -> TermList [- plus(t1,t2) ]\n\
\\n\
\RULES\n\
\\n\
\add(bot(), u) -> u\n\
\add(u, bot()) -> u\n\
\add(u\\bot(), v\\bot()) -> plus(u, v)\n\
\// add(var(s1), var(s2)) -> plus(var(s1), var(s2))\n\
\// add(var(s1), appl(g,l2)) -> plus(var(s1), appl(g,l2))\n\
\// add(var(s1), plus(v1,v2)) -> plus(var(s1), plus(v1,v2))\n\
\// add(appl(f,l1), var(s2)) -> plus(appl(f,l1), var(s2))\n\
\// add(appl(f,l1), appl(g,l2)) -> plus(appl(f,l1), appl(g,l2))\n\
\// add(appl(f,l1), plus(v1,v2)) -> plus(appl(f,l1), plus(v1,v2))\n\
\// add(plus(u1,u2), var(s2)) -> plus(plus(u1,u2), var(s2))\n\
\// add(plus(u1,u2), appl(g,l2)) -> plus(plus(u1,u2), appl(g,l2))\n\
\// add(plus(u1,u2), plus(v1,v2)) -> plus(plus(u1,u2), plus(v1,v2))\n\
\\n\
\complement(sig, u, var(s)) -> bot()\n\
\complement(sig, u, bot()) -> collectPlus(u)\n\
\complement(sig, u, plus(v1,v2)) -> complement(sig, complement(sig,u,v1), v2)\n\
\complement(sig, var(s), appl(f,l)) -> complement(sig, generate(sig), appl(f,l))\n\
\complement(sig, bot(), appl(f, l)) -> bot()\n\
\complement(sig, plus(u1,u2), appl(f,l)) -> add(complement(sig, u1, appl(f,l)), complement(sig, u2, appl(f,l)))\n\
\complement(sig, appl(name(f),l1), appl(name(g),l2)) -> ite(eq(f,g), interleave(name(f), l1, l2, nil(), sig), collectPlus(appl(name(f), l1)))\n\
\\n\
\generate(sig(f,n,sig)) -> add(build(f,n,nil()), generate(sig))\n\
\generate(empty()) -> bot()\n\
\\n\
\build(f, z(), l) -> appl(f, l)\n\
\build(f, s(n), l) -> build(f, n, cons(var(name(n)), l))\n\
\\n\
\interleave(f, cons(u1,l1), cons(u2,l2), rl, sig) -> add(interleave(f, l1, nil(), cons(complement(sig, u1, u2), rl), sig), interleave(f, l1, l2, cons(u1,rl), sig))\n\
\interleave(f, cons(u1,l1), nil(), rl, sig) -> interleave(f, l1, nil(), cons(u1,rl), sig)\n\
\interleave(f, nil(), l2, cons(u, rl), sig) -> split(f, collectPlus(u), rl, nil())\n\
\interleave(f, nil(), l2, nil(), sig) -> bot()\n\
\\n\
\split(f, plus(t1,t2), tl, rl) -> add(split(f, t1, tl, rl), split(f, t2, tl, rl))\n\
\split(f, bot(), tl, rl) -> bot()\n\
\split(f, t\\(bot() + plus(t1,t2)), cons(u,tl), rl) -> split(f, collectPlus(u), tl, cons(t,rl))\n\
\// split(f, appl(g, ul), cons(u,tl), rl) -> split(f, collectPlus(u), tl, cons(appl(g,ul),rl))\n\
\// split(f, var(s), cons(u,tl), rl) -> split(f, collectPlus(u), tl, cons(var(s),rl))\n\
\split(f, t\\(bot() + plus(t1,t2)), nil(), rl) -> appl(f, reverse(rl, cons(t, nil())))\n\
\// split(f, appl(g, ul), nil(), rl) -> appl(f, reverse(rl, cons(appl(g, ul), nil())))\n\
\// split(f, var(s), nil(), rl) -> appl(f, reverse(rl, cons(var(s), nil())))\n\
\\n\
\collectPlus(plus(u1, u2)) -> add(collectPlus(u1),collectPlus(u2))\n\
\collectPlus(appl(f, nil())) -> appl(f, nil())\n\
\collectPlus(appl(f, cons(t, tl))) -> split(f, collectPlus(t), tl, nil())\n\
\collectPlus(var(s)) -> var(s)\n\
\collectPlus(bot()) -> bot()\n\
\\n\
\reverse(cons(t,l), rl) -> reverse(l, cons(t, rl))\n\
\reverse(nil(), rl) -> rl"
