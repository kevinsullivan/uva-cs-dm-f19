import .prop_logic

/-
A logic is a "formal language" with
a mathematically defined syntax and a
mathematically defined semantics. The
syntax of a language defines the set
of legal expressions in the language
(sometimes called formula, well-formed
formula, sentences, etc). The semantics
then explains how to give a meaning to
each such expression.


In this unit, we formalize the syntax
and semantics of our first example of
a complete logic: a simple logic called
propositional logic.

The *syntactic* terms of propositional
logic again fall in three categories:
- there are two literal terms, which we
will call pTrue and pFalse
- there are variable terms
- and there are application terms, in
which propositional logic connectives
are applied to smaller terms to create
larger ones. These connectives are the
familiar connectives of Boolean algebra:
and (∧), or (∨), not (¬), and so forth.

Examples of propositional logic terms
thus include:
- pTrue             -- literal
- pFalse            -- literal
- and pTrue pFalse  -- application
- X                 -- variable
- Y                 -- variable
- Z                 -- variable
- X ∨ Y             -- application: or X Y
- (X ∨ Y) ∧ (X ∧ Z) -- etc.
- (X ∨ Y) ∧ (X ∧ pTrue)
- etc

The semantic domain of discourse, in which
such expressions are given meaning, is the 
set of Boolean truth values, {true, false}.
The semantics of propositional logic assigns
a simple Boolean truth value to each such
propositional logic expression. 

In this unit, we will define "eval" to be
a function that takes an expressions and
returns its meaning as a Boolean value.
(As we'll see shortly, the eval function
will have to take one more argument in
order to deal with variable expressions).

Here are the rules for how eval works:

LITERAL TERMS

To the literal, pTrue, the semantic
"evaluation" function assigns the truth
value, true. To pFalse, it assigns the
truth value false. In other words, we
define eval(pFalse) to be the bool, ff,
and eval (pTrue) to be the bool, tt.

VARIABLE TERMS

To evaluate a variable expression, such
as X, or to evaluate an expression with
several variables, such as X ∧ Y, we need
an addition piece of data: what Boolean
truth value each such variable has. 
We call this data an *interpretation*.
We will represent it as a function, interp,
from variables to Boolean truth values. 
The semantic meaning of the syntactic
variable term, X, is then interp(X).
I.e., eval(X) is defined as interp(X).

There are many possible interpretations 
for a given (non-empty) set of variables.
Self-test: How many interpretations are
there for a single variable, X? How many
interpretations are possible for a set
of variables {X_i} of size n?

APPLICATION TERMS

Application terms are built inductively
by applying proposition logic connectives
to smaller terms. For example, if e1 and
e2 are terms (whether literal, variable,
or application), then so are (and e1 e2),
(or e1 e2), (not e1), etc.

Our intention is that the semantics of 
such syntactic terms should reflect the
usual Boolean algebraic meaning of the
connectives. So, for example, if e1 and 
e2 are expressions, then so is (and e1 
e2), and we wish to evaluate this as
true if and only if both e1 and e2
evaluate to true.

We thus define eval to work recursively
on such expressions. We evaluate the truth
of e1 and of e2 and then apply the *bool*
and operator (as distinct from the and
logical connective) to the results to
determine the truth value of (and e1 e2).
-/

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


-- names for a few
def varX := mkVar 0
def varY := mkVar 1
def varZ := mkVar 2


-- Operators (connectives)
#check pNot     -- unary
#check pAnd     -- binary
#check pOr      -- binary


-- Expressions

-- Literal
#check litExp ff
#check litExp tt
#check pFalse
#check pTrue

-- Variable
#check varExp varX
#check varExp varY
def X : pExp:= varExp varX
def Y : pExp := varExp varY
def Z : pExp := varExp varZ
#check X
#check Y

-- Operator/application
#check unOpExp notOp pTrue
#check unOpExp notOp

-- with shorthands
#check pNot pTrue
#check pNot X
#check binOpExp andOp X Y
#check binOpExp andOp
#check pAnd X Y
#check pOr X Y

-- finally, logical expressions!
#check pTrue
#check ¬ pTrue
#check ¬ pFalse
#check X
#check ¬ X
#check Y
#check X ∧ Y
#check X ∨ Y
#check ¬ (X ∧ Y)
#check ¬ (X ∧ Y) ∨ (¬ X ∨ ¬ Y) 

/-
You have now defined the syntax of the
formal language, propositional logic!
You can now check syntactic correctness
of expressions.
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

-- Interpretations

def allFalse : var → bool
| _ := ff

def allTrue : var → bool
| _ := tt

def anInterp: var → bool 
  | (mkVar 0) := tt
  | (mkVar 1) := ff
  | (mkVar 2) := tt
  | (mkVar _) := ff

-- interpretation

#eval allFalse varX
#eval allTrue varX
#eval anInterp varX
#eval anInterp varY


-- Interpretation of operators

#check interpUnOp notOp 
#eval (interpUnOp notOp) tt 
#eval interpBinOp andOp tt ff
#eval interpBinOp andOp tt tt

-- evaluation of expressions

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
To formalize a semantics for our
realization of propositional logic,
we need to formally define what we
mean by an interpretation.

An interpretation in propositional 
logic is a function from propositional
variables to corresponding (Boolean)
truth values. An interpretation tells
us what each variable "means" -- i.e.,
whether it means true, or false. 

We now define a name for the type
of an interpretation (pVar → bool).
Then we present several examples of
interpretations.
-/

-- Semantics

/-
We now define a semantics for our
language in the form of a function
that, when given any expression in
our language *and* an interpretation
for the variables that might appear
in it, evaluates its truth value and
returns it as a result.

The definition is by cases, i.e., 
with one rule for each possible form
(constructor) of expression.

Note: Lean "overloads" logical
operator notations, such as ∧, ∨, 
and ¬. Here they are applied not to
values of type Prop, but to values 
of type bool, where they have their
usual means from Boolean algebra.
-/

/-
And now we have a formal language, with
a syntax, interpretations, and semantics.
Let's evaluate some of our expressions
under varying interpretations.
-/


/-
So there you have it: a complete
formal definition of the syntax,
interpretation, and semantics of
propositional logic, in Lean, with
a nice "surface syntax," to boot.
(Ok, it's complete except for the
definitions for the other logical
connectives. You will add some of
them in homework and on the exam.)
-/

/-
From here, we can define richer
functions, such as functions that
analyze expressions; and we can
even state and prove theorems 
about our language.
-/

/-
Let's define a function that 
returns the set of variables 
in a given pExp. This will be
useful in the future.
-/

/-
We start by defining a recursive 
helper function that adds all the 
variables in given expression to 
the given, often already non-empty, 
set of variables.

Understand the type and purpose of
this function, then go on to read 
the following main function. Study
its purpose, type, and implementation,
then come back for a deeper look at 
how this function is implemented.
Learn to use functions knowing only
their type and purpose, ignoring, at
least at first, their implementation
details. Pratice mental abstracting.

We implement (prove) this recursive 
function (type) by case analysis on 
possible forms of the given pExp.
-/
/-
Main function: a non-recursive function
that passes an initially empty set of
variables to the helper function and 
then gets back a set of all, and only,
the variables in the given expression.
-/
/-
Examples of its use
-/
#reduce vars_in_exp (X ∧ Y)
-- A predicate for set {X,Y}

/-
Another example
-/
#reduce vars_in_exp (X ∧ Z)

/-
EXERCISE: Write a function that when
given an expression, e, returns the 
"nesting depth" of the expression. The
nesting depth of a literal or variable
expression is 1. The depth of a (not e) 
expression is 1 + the depth of e. And
the depth of an (and e1 e2) expression
is 1 + the max of the depths of e1 and
e2. You can use the Lean-provided max 
function in your answer.
-/

#reduce max 5 7
#reduce max 7 5

/-
We can also prove theorems about
our language in general. Here's a
proof that evaluation under a given
interpretation is "deterministic:: 
it always produces the same result.

This is really just a corollary of
the facts that (1) functions in Lean 
are single valued and (2) we defined 
the semantics of expressions with a
function. There's one and only one 
answer for the value of any given
expression.
-/

theorem pEval_deterministic :
∀ e : pExp, 
∀ i : pInterp,
∀ v1 v2 : bool,
v1 = pEval e i → v2 = pEval e i → v1 = v2 :=
begin
intros e i v1 v2 h_v1 h_v2,
rw h_v1, 
rw h_v2,
end


/-
We can also prove theorems ("reason
about") particular expressions, or
certain classes of expressions, in 
our language. For example, if X_exp 
is any variable expression, then the 
expression (X_exp ∧ (¬ X_exp)) is 
false under any interpretation. We
can easily prove this proposition.
-/

theorem contra :
∀ V : pVar,
∀ i : pInterp,
pEval 
    ((mk_var_pexp V) ∧ ¬ (mk_var_pexp V)) i = ff 
:=
begin
intros X i,
simp [pEval],
-- case analysis on result of function!
cases (i X),
left, apply rfl,
right, apply rfl,
end

/-
Note that it is quantified over all
possible interpretations: over all
possible functions from pVar → bool.
Lean supports what is called higher
order predicate logic. Quantifying
over functions and relations is ok
in a higher-order predicate logic. 
It is not allowed in the first-order
predicate logic of everyday math and
computer science. Here you can see
that it gives you great expressive
power to be able to quantify over
functions. It gives us a way to say,
"under any possible interpretation",
which is exactly what we need to be
able to say to define satisfiability,
validity, unsatisfiability, etc.
-/



/-
Exercise: Prove that for any 
variable, V, the logical expression
(mk_var_exp V) ∨ (¬ (mk_var_exp V))
always evaluates to true.
-/

def valid (e : pExp) : Prop :=
    ∀ i : pInterp, pEval e i = tt

/-
An expression in propositional logic
is unsatisfiable if it does'ot evaluate 
to true under any interpretation.
-/

def unsatisfiable (e : pExp) : Prop :=
    ∀ i, pEval e i = ff

/-
You could also have said there does not
exist an i that makes (pEval e i) = tt.
-/

/-
An interpretation that makes an
expression, e, evaluate to true,
is said to be a "model" of that
expression. Here's a predicate
asserting that i is a model of e.
-/

def isModel (i: pInterp) (e : pExp) :=
    pEval e i = tt

/-
An expression is said to be satisfiable 
if there is at least one interpretation 
under which it evaluates to true.
-/
def satisfiable (e : pExp) : Prop :=
    ∃ i, isModel i e

/-
Example: X ∧ ¬ X is unsatisfiable.
-/

example : unsatisfiable (X_exp ∧ (¬ (X_exp))) :=
begin
unfold unsatisfiable,
intro i,
rw pEval, -- you can do this
rw pEval, -- and do it again
cases (pEval X_exp i), -- cool!
trivial,
trivial,
end

/-
EXERCISE: Once you've extended
our logic with an or operator,
formulize and prove the proposition
that (our rendering of) X ∨ (¬ X)
is valid.

EXERCISE: Prove the proposition
that (X ∨ Y) ∧ Z is satisfiable.
Hint: You'll need a witness. There
is an element of search involved
in solving a problem like this.
-/

/-
EXERCISE: Write a SAT solver based
on what we've done here.
-/

-- m'th bit from right in binary rep of n
def mrbn: ℕ → ℕ → bool 
| 0 n := n % 2 = 1
| (nat.succ m') n := mrbn m' (n/2) 

/- smoke test
#reduce mrbn 0 15
#reduce mrbn 2 15
#reduce mrbn 2 15
#reduce mrbn 3 15
#reduce mrbn 4 15
#reduce mrbn 5 15
-/

/-
The mth canonical interpretation
among the 2^n-1 interpretations
for a set of variables of size n.

The values of the first n-indexed
variables in the mth interpretation
are determined by the bits in the 
binary representation of m. The
leftmost bit gives the value for 
the variable with index 0. Each
bit to the left gives the value of
the next indexed variable. All 
subsequent values are ff. m thus 
effectively enumerates the 2^n 
interpretations on the n first 
variables in the index set of all
variables. 
-/

def mthInterpOf2toN (m n: ℕ) : pInterp :=
    if (m >= 2^n)
    then falseInterp 
    else
    λ v : pVar, 
        match v with
        | (pVar.mk i) := 
        if i >= n then 
        ff 
        else 
        (mrbn i m)
        end

/-
Examples:
-/

#reduce pEval and_X_Y_exp (mthInterpOf2toN 3 3)

-- unincorporated

#reduce mthInterpOf2toN 3 5

def first_n_true_inter (n : ℕ) : pInterp :=
λ v, 
    match v with
    | (pVar.mk n') := if n' < n then tt else ff
    end

def all_models (e : pExp) :=
    { m | isModel m e}


def sat_solve (e : pExp) : option pInterp :=
none


