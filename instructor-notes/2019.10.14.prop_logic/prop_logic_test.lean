import .prop_logic

/-
This file contains example
and test code for each of the
constructs defined in the
prop_logic.lean implementation
of the syntax and semantics of
propositional logic.
-/

-- open namespaces
open prop_logic
open prop_logic.var
open prop_logic.unOp
open prop_logic.binOp
open prop_logic.pExp


/-
    **************
    *** SYNTAX ***
    **************
-/


-- Variables

#check mkVar
#check mkVar 0
#check mkVar 1
#check mkVar 2
#check mkVar 3


-- nicer names for a few variables
def varX := mkVar 0
def varY := mkVar 1
def varZ := mkVar 2
def varW := mkVar 4



/-
Nicer names for a few
variable expressions. We
define X, Y, Z, and W to be
variables expressions that
we can use in writing larger
propositional logic expressions.
-/

#check varExp varX
#check varExp varY

def X : pExp:= varExp varX
def Y : pExp := varExp varY
def Z : pExp := varExp varZ
def W : pExp := varExp (mkVar 3)


-- Operators (connectives)
#check pNot     -- unary
#check pAnd     -- binary
#check pOr      -- binary

#check pNot X
#check pAnd X Y
-- Expressions

-- Literal
#check litExp ff
#check litExp tt
#check pFalse
#check pTrue

-- Variable
#check X
#check Y
#check Z
#check W

-- Operator/application
#check unOpExp
#check unOpExp notOp
#check unOpExp notOp pTrue

-- with shorthands
#check pNot
#check pNot pTrue
#check pNot X

#check binOpExp 
#check binOpExp andOp
#check binOpExp andOp X Y

#check pAnd X Y
#check pOr X Y

/-
We've now defined an "abstract
syntax" for propositional logic
expressions. It's somewhat arcane
and not exactly how we'd like to
write expressions. For example,
we'd generally prefer to write
(X ∧ Y) instead of (pAnd X Y). 
The solution is to define what
Lean calls "notations" that allow
us to write the former and to 
have Lean automatically "desugar"
(covert) them into the latter.
See the definitions of notations
in the prop_logic.lean file. With
these notations defined, we now 
have a complete and conventional
concrete syntax for propositional
logic! 
-/

#check pTrue
#check litExp tt

#check ¬ pTrue
#check pNot pTrue
#check pNot (litExp tt)
#check (unOpExp notOp) (litExp tt)

#check ¬ pFalse
#check X
#check ¬ X
#check Y
#check X ∧ Y
#check X ∨ Y
#check ¬ (X ∧ Y)

-- All of these are equivalent!
#check ¬ (X ∧ Y) 
#check pNot (X ∧ Y)
#check (unOpExp notOp) X ∧ Y
#check (unOpExp notOp) (binOpExp andOp X Y)
#check (unOpExp notOp) (binOpExp andOp (varExp varX) (varExp varY))
#check (unOpExp notOp) (binOpExp andOp (varExp (mkVar 0)) (varExp (mkVar 1)))
-- first line is concrete syntax
-- last line is abstract syntax


#check ¬ (X ∧ Y) ∨ (¬ X ∨ ¬ Y) 

/-
Not only can we write 
syntactically correct
expressions, but we we
try to write (construct)
incorrect expressions, it
will not work, because they
will not be valid terms
of type pExp.
-/

#check ¬ (X ∧ Y) ∨ (X ∨ Z) -- correct
#check ¬ (X ∧ Y) ∨ (X ∨ )  -- error
#check ¬ X ¬ Y             -- error
#check pTrue pFalse        -- error


/-
    *****************
    *** SEMANTICS ***
    *****************
-/

-- Three examples of interpretations

-- Every variable has value, "ff"
def allFalse : var → bool
| _ := ff

-- Every variable has value, "tt"
def allTrue : var → bool
| _ := tt

-- Variables have values as specified
def anInterp: var → bool 
  | (mkVar 0) := tt -- varX
  | (mkVar 1) := ff -- varY
  | (mkVar 2) := tt -- varZ
  | (mkVar 3) := ff -- varW
  | (mkVar _) := tt -- otherwise

/-
Note that an interpretation maps
variables (objects of type var) to
values. An interpretation does not
map pExp "variable expressions" to
values, at least not directly. 
Rather, our evaluation function
given a variable expression pExp
[(varExp v) for some v], extracts
the variable v from the expression,
and applies an interperation to
that "var" v to get a value for
the variable expression given the
specified interpretation function.
-/

-- examples: apply interps to vars

#eval allFalse varX
#eval allTrue varX
#eval anInterp varX
#eval anInterp varY


-- Interpretation of operators

#check interpUnOp  
#check interpUnOp notOp         -- bnot
#eval (interpUnOp notOp) tt     -- ff
#check interpBinOp
#check interpBinOp andOp        -- band
#eval (interpBinOp andOp) tt ff   -- ff
#eval (interpBinOp orOp) tt ff   -- tt
#eval interpBinOp andOp tt ff   --ff
#eval interpBinOp andOp tt ff   --ff
#eval interpBinOp andOp tt tt   -- tt

/-
Now we finally have both a beautiful
concrete syntax for our implementation
of the language of propositional logic, 
and definition of its semantics that 
we can use to automatically evaluate
the truth meaning of any expression if
we are also given an interpretation of
the variables. Here are examples. In 
each case, the first argument to pEval 
is an expression and the second is a
specific interpretation function.
-/

#eval pEval pTrue allTrue
#eval pEval pTrue allFalse
#eval pEval X allTrue
#eval pEval Y allFalse
#eval pEval X anInterp
#eval pEval Y anInterp
#eval pEval (X ∧ Y) allTrue
#eval pEval (X ∧ Y) allFalse
#eval pEval (X ∧ Y) anInterp
#eval pEval (X ∨ Y) anInterp
#eval pEval (X ∧ Z) anInterp
#eval pEval (¬ (X ∧ Z)) anInterp
#eval pEval (¬ (X ∧ Y) ∨ (¬ X ∨ ¬ Y)) anInterp
#eval pEval (¬ (X ∧ Y) ∨ (¬ X ∨ ¬ Y)) allTrue

/-
    *** YAY! ***
-/
