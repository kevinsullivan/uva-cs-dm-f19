namespace prop_logic

/- [25 points total, as indicated below]

This assignment has five problems. The first
is to extend our propositional logic syntax
and semantics to support the three additional
connectives, exclusive or (⊕), implies (which 
we will write as ⇒), and if and only iff (↔).
We first give you the definitions developed
in class. You are to extend/modify them to
support expressions with the new connectives.
The remaining problems use this definition of
our language of expressions in propositional
logic.  
-/


/--/
    **************
    *** SYNTAX ***
    **************
-/

inductive var : Type 
| mkVar : ℕ → var

inductive unOp : Type
| notOp

inductive binOp : Type
| andOp
| orOp
/-HW 5 points]-/
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
/-HW- [5 points]-/
def pXor := binOpExp xorOp
def pImpl := binOpExp implOp
def pIff := binOpExp iffOp
/-HW-/

-- conventional notation

notation e1 ∧ e2 :=  pAnd e1 e2
notation e1 ∨ e2 :=  pOr e1 e2
notation ¬ e := pNot e

#print ⇒  


/-HW- [5 points] -/
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

/-

-/

/-HW [5 points] -/
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
/-HW [5 points] -/
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
#2 [5 points]. Define X, Y, and Z to be 
variable expressions with no "aliases". That 
is each name should be bound to a distinct
variable expression term. Hint: Just look
at the prop_logic_test.lean file to 
remind yourself what we did in class.
-/

def X : pExp := varExp (mkVar 0)
def Y : pExp := varExp (mkVar 1)
def Z : pExp := varExp (mkVar 2)



/- [25 points total, as indicated]

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
For the remaining problems, use the 
variables expressions, X, Y, and Z, 
as already defined. Use parentheses
if needed to group sub-expressions.
-/

/-
A. [5 points]

If it's raining and the streets are
wet then it's raining.
-/

def p2 : pExp := (X ∧ Y) ⇒ X

/- [5 points] 

B. If it's raining and the streets
are wet, then the streets are wet
and it's raining. 
-/

def p3 := (X ∧ Y) ⇒ (Y ∧ X)


/- [5 points]

C. If it's raining then if the
streets are wet then it's raining
and the streets are wet.
-/
def p4 := X ⇒ (Y ⇒ (X ∧ Y))

/- [5 points]

D. If it's raining then it's
raining or the moon is made of
green cheese.
-/
def p5 := X ⇒ (X ∨ Y)

/- [5 points] 

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

/- [5 points]
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
B. [10 points]
-/

#check ((X ⇒ Y) ∧ (Y ⇒ X)) ⇒ (X ⇒ Z)

/-

THE ORIGINAL ANSWER KEY GAVE ANSWER FOR A DIFFERENT QUESTION.
THIS ANSWER IS CORRECT.

X   Y   Z   X ⇒ Y   Y ⇒ X   (X ⇒ Y) ∧ (Y ⇒ X)   X ⇒ Z   Result
-   -   -   -----   -----   -----------------   -----   ------
T   T   T   T       T       T                   T       T
T   T   F   T       T       T                   F       F
T   F   T   F       T       F                   T       T 
T   F   F   F       T       F                   F       T
F   T   T   T       F       F                   T       T
F   T   F   T       F       F                   T       T
F   F   T   T       T       T                   T       T
F   F   F   T       T       T                   T       T

This formula is NOT valid.
-/

/-
C. [5 points]
-/
#check pFalse ⇒ (X ∧ ¬ X)

/-

Truth table answers omitted here and below. Maybe a TA will 
fill in answers. 

This proposition is valid.
-/


/-
D. [5 points]
-/

#check pTrue ⇒ (X ∧ ¬ X)

-- Unsatisfiable.


/-
E. [5 points]
-/

#check (X ∨ Y) ∧ X ⇒ ¬ Y

-- Satisfiable but not valid.


/- [15 points total]

#5. Find and present an interpretation
that causes the following proposition
to be satisfied (to evaluate to true).

(X ∨ Y) ∧ (¬ Y ∨ Z)

Answer [5 points]:

Next determine how many interpretations
satisfy it.

Answer [10 points]:  

X Y Z   (X ∨ Y)     (¬ Y or Z)  (X ∨ Y) ∧ (¬ Y ∨ Z)

T T T   T           F           F
T T F   T           F           F
T F T   T           F           F
T F F   T           T           T   * model
F T T   T           T           T   * model
F T F   T           F           F
F F T   F           T           F
F F F   F           T           F

ANSWER: Two interpretations satisfy the formula,
as per the truth table above, which gives the two
satisfying assignments of values to the variables
(models).
-/

end prop_logic

