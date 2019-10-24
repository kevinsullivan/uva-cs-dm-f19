namespace prop_logic

/-
    ********************
    *** INTRODUCTION ***
    ********************
-/

/-
A logic is a "formal language" with
a mathematically defined *syntax* and
a mathematically defined *semantics*. 

The syntax of a language defines its 
set of syntactically "well formed"
expressions. Its semantics defines a
meaning for each such expression. 

The expressions of a formal language 
are also sometimes also called well-formed
formulae (abbreviated as WFFs), formulae,
or sentences. 

In this unit, we formalize the syntax
and semantics of our first example of
a logic; namely propositional logic.

An expression in this language is one of
the following: (1) a literal "true" or a
literal "false" expression; (2) for any
variable, v, the "variable expression", 
(varExp v); (3) for any expressions, e1
and e2, the expressions ¬ e1, e1 ∧ e2, or
e1 ∨ e2. The symbols, ¬, ∧, and ∨, which
are pronounced not, and, and or, are
called connectives. 

Because connectives connect one or more
smaller expressions into larger ones, 
they give rise to expressions such as 
¬ e1, e1 ∧ e2, and e1 ∨ e2, where e1 and 
e2 can themselves be arbitrarily simple
or complex expression: literal, variable,
or connective. 

The semantic domain for propositional
logic is the algebra of Boolean truth
values. We then define the semantics of
propositional logic as a function that
takes an expression as an argument, along
with a second argument, an interpretation,
and returns a Boolean value that is taken
as "the meaning of that expression under
that interpretation."

To the literal true and false expressions,
our semantics assigns the corresponding
Boolean truth values, true and false. 

The assignmenting of a truth value to a 
variable expression, (varExp v), depends
on a function, an interpretation, that
maps variables to Boolean values, thereby
specifying a Boolean value for each such
variable, and thus variable expressions. 

Finally, the assignment of a truth value
to an operator expression works by recursive
semantic evaluation of each sub-expression,
followed by the application of the Boolean
function corresponding to the connective,
to the results for those sub-expressions.

In this unit, we define "pEval" to 
be a function that takes any expression
along with an intepretation function and
that returns the Boolean "meaning" of 
that expression under that interpretation.
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
| xorOp
| implOp
| iffOp

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
def pXor := binOpExp xorOp
def pImpl := binOpExp implOp
def pIff := binOpExp iffOp

-- conventional notation

notation e1 ∧ e2 :=  pAnd e1 e2
notation e1 ∨ e2 :=  pOr e1 e2
notation ¬ e := pNot e
notation e1 ⇒ e2 := pImpl e1 e2
notation e1 ⊕ e2 := pXor e1 e2
notation e1 ↔ e2 := pIff e1 e2

/-
    *****************
    *** SEMANTICS ***
    *****************
-/

def interpUnOp : unOp → (bool → bool) 
| notOp := bnot

def bimpl : bool → bool → bool
| tt ff := ff
| _ _ := tt

def biff : bool → bool → bool
| tt tt := tt
| ff ff := tt
| _ _ := ff

def interpBinOp : binOp → (bool → bool → bool) 
| andOp := band
| orOp := bor
| xorOp := bxor
| implOp := bimpl
| iffOp := biff

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


end prop_logic

