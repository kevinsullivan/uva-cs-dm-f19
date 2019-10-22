namespace prop_logic

/-
1. Extend our syntax and semantics
for propositional logic to support
the xor, implies, and iff and only
iff connectives/operators.

A. Add support for the exclusive or
connective/operator. Define the symbol, 
⊕, as an infix notation.

Here are specific steps to take for the
exclusive or connective, as an example.

1. Add new binary connective, xorOp
2. Add pXor as shorthand for binOpExp xorOp
3. Add ⊕ as an infix notation for pXor
4. Specify the interpretation of ⊕ to be bxor
5. Extend interpBinOp to handle the new case 

Then add support for the implies connective,
using the symbol, ⇒, as an infix operator.
We can't use → because it's reserved by Lean
and cannot be overloaded. Lean does not have 
a Boolean implies operator (analogous to bor),
so you will have to define one. Call it bimpl.

Finally add support for if and only iff. Use
the symbol ↔ as an infix notation. You will
have to define a Boolean function as Lean 
does not provide one for iff. Call it biff.

Here is the code as developed in class.
Now review the step-by-step instructions,
and proceed to read and midify this logic
as required. We've bracketed areas where
new material will have to be added. 
-/

/-  *** SYNTAX *** -/

inductive var : Type 
| mkVar : ℕ → var

inductive unOp : Type
| notOp

inductive binOp : Type
| andOp
| orOp
/-HW-/
| xorOp
| implOp
| iffOp
/-HW-/

inductive pExp : Type
| litExp : bool → pExp
| varExp : var → pExp
| unOpExp : unOp → pExp → pExp
| binOpExp : binOp → pExp → pExp → pExp

open var
open pExp
open unOp
open binOp

-- Shorthand notations
def pTrue := litExp tt
def pFalse := litExp ff
def pNot := unOpExp notOp
def pAnd := binOpExp andOp
def pOr := binOpExp orOp
/-HW-/
def pXor := binOpExp xorOp
def pImpl := binOpExp implOp
def pIff := binOpExp iffOp
/-HW-/

-- conventional notation

notation e1 ∧ e2 :=  pAnd e1 e2
notation e1 ∨ e2 :=  pOr e1 e2
notation ¬ e := pNot e

/-HW-/
notation e1 ⇒ e2 := pImpl e1 e2
notation e1 ⊕ e2 := pXor e1 e2
notation e1 ↔ e2 := pIff e1 e2
/-HW-/

/-
    *****************
    *** SEMANTICS ***
    *****************
-/

def interpUnOp : unOp → (bool → bool) 
| notOp := bnot

/-HW-/
def bimpl : bool → bool → bool
| tt ff := ff
| _ _ := tt

def biff : bool → bool → bool
| tt tt := tt
| ff ff := tt
| _ _ := ff
/-HW-/

def interpBinOp : binOp → (bool → bool → bool) 
| andOp := band
| orOp := bor
/-HW-/
| xorOp := bxor
| implOp := bimpl
| iffOp := biff
/-HW-/

/-
Given a pExp and an interpretation
for the variables, evaluate the pExp
to determine its Boolean truth value.
-/
def pEval : pExp → (var → bool) → bool 
| (litExp b) i := b
| (varExp v) i := i v
| (unOpExp op e) i := 
    (interpUnOp op) (pEval e i)
| (binOpExp op e1 e2) i := 
     (interpBinOp op)
        (pEval e1 i) 
        (pEval e2 i)


/-
#2. Define X, Y, and Z to be variable
expressions with no "aliases". That is
each name should be bound to a distinct
variable expression term. Hint: Just look
at the prop_logic_test.lean file to 
remind yourself what we did in class.
-/

def X : pExp := _
def Y : pExp := _
def Z : pExp := _



/-
#3. Here are some English language 
sentences that you are to re-express
in propositional logic. Here's one
example.
-/

/-
EXAMPLE:

Formalize the following proposition,
as a formula in propositional logic:
If it's raining then it's raining.
-/

-- Solution

def R : pExp := varExp (mkVar 4)
def p1 : pExp := R ⇒ R

/-
Explanation: We first choose to represent
the smaller proposition, "it's raining", 
by the variable expression, R. We then
formalize the overall natural language
expression, if R then R, as the formula,
R ⇒ R.

Note: R ⇒ R can be pronounced as any of:
- if R is true then R is true 
- if R then R
- the truth of R implies the truth of R
- R implies R  

The second and fourth pronounciations
are the two that we prefer to use. 
-/

/-
For the remaining problems, please
use the variables expressions, X, Y, 
and Z, which we have already defined.
Use parentheses as needed to ensure
that your formal propositions express
what you mean for them to express. 
-/

/-
A.

If it's raining and the streets are
wet then it's raining.
-/

def p2 : pExp := (X ∧ Y) ⇒ X

/-
B. If it's raining and the streets
are wet, then the streets are wet
and it's raining. 
-/

def p3 := (X ∧ Y) ⇒ (Y ∧ X)


/-
C. If it's raining then if the
streets are wet then it's raining
and the streets are wet.
-/
def p4 := X ⇒ (Y ⇒ (X ∧ Y))

/-
D. If it's raining then it's
raining or the moon is made of
green cheese.
-/
def p5 := X ⇒ (X ∨ Y)

/-
E. If it's raining, then if it's
raining implies that the streets 
are wet, then the streets are wet.
-/
#check X ⇒ (X ⇒ Y) ⇒ Y


/-
#4. For each of the propositional
logic expressions below, write a truth
table and based on your result, state
whether the expression is unsatisfiable,
satisfiable but not valid, or valid. 

Here's an example solution for the
expression, (X ∧ Y) ⇒ Y.

X   Y   X ∧ Y   (X ∧ Y) ⇒ Y
-   -   -----   -----------
T   T   T       T ⇒ T = T
T   F   F       F ⇒ F = T
F   T   F       F ⇒ T = T
F   F   F       F ⇒ F = T

The proposition is thus valid.
-/

/-
A. After the #check give your answer
for the checked proposition. Important
to know: implies is right associative.
-/


#check (X ⇒ Y) ⇒ (¬ X ⇒ ¬ Y)

/-

X   Y   X ⇒ Y   ¬ X ⇒ ¬ Y   Result
-   -   -----   ---------   ------
T   T   T       T               T
T   F   F       T               T
F   T   T       F               F
F   F   T       T               T

Formula is satisfiable but not valid.

-/


/-
B.
-/

#check ((X ⇒ Y) ∧ (Y ⇒ X)) ⇒ (X ⇒ Z)

/-
X   Y   Z   X ⇒ Y   Y ⇒ Z   (X ⇒ Y) ∧ (Y ⇒ X)   X ⇒ Z   Result
-   -   -   -----   -----   -----------------   -----   ------
T   T   T   T       T       T                   T       T
T   T   F   T       F       F                   F       T
T   F   T   F       T       F                   T       T 
T   F   F   F       T       F                   F       T
F   T   T   T       T       T                   T       T
F   T   F   T       F       F                   T       T
F   F   T   T       T       T                   T       T
F   F   F   T       T       T                   T       T

This formula is valid.
-/

/-
C.
-/
#check pFalse ⇒ (X ∧ ¬ X)

/-

Truth table answers omitted here and below. Maybe a TA will 
fill in answers. 

This proposition is valid.
-/


/-
D.
-/

#check pTrue ⇒ (X ∧ ¬ X)

-- Unsatisfiable.


/-
E.
-/

#check (X ∨ Y) ∧ X ⇒ ¬ Y

-- Satisfiable but not valid.


/-
#5. Find and present an interpretation
that causes the following proposition
to be satisfied (to evaluate to true).

(X ∨ Y) ∧ (¬ Y ∨ Z)

Answer:

Next determine how many interpretations
satisfy it.

Answer; 
-/



end prop_logic

