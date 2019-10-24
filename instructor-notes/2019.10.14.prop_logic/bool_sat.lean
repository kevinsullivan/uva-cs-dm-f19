import .prop_logic 

open prop_logic 

open prop_logic.var
open prop_logic.unOp
open prop_logic.binOp
open prop_logic.pExp

/-
Recursive helper function for the 
following function. The purpose of
these functions is to return a
list of the variables in a given
pExp. 

This function takes a pExp and a 
list of variables already found, 
and list extended with the variables
in the given pExp.
-/
def vars_in_exp_helper: 
    pExp → list var → list var
| (litExp _) s := s
| (varExp v) s := list.cons v s
| (unOpExp op e) s := 
    list.append 
        s 
        (vars_in_exp_helper e s)
| (binOpExp op e1 e2) s := 
    list.append 
        s
        (
            list.append
                (vars_in_exp_helper e1 s)
                (vars_in_exp_helper e2 s)
        )
    

/-
Main function: call the helper with 
an initially empty set of variables
found so far.
-/
def vars_in_exp (e: pExp) : list var :=
    vars_in_exp_helper e []

def X : pExp:= varExp (mkVar 0)
def Y : pExp := varExp (mkVar 1)
def Z : pExp := varExp (mkVar 2)
def W : pExp := varExp (mkVar 3)

def anExp : pExp := (X ∧ Y) ∨ Z
#reduce vars_in_exp anExp 


/-
    *****************************
    *** SATISFIABILITY solver ***
    *****************************
-/

-- m'th bit from right in binary rep of n
def mrbn: ℕ → ℕ → bool 
| 0 n := n % 2 = 1
| (nat.succ m') n := mrbn m' (n/2) 

#eval mrbn 1 7

/-
The mth canonical interpretation
among the 2^n interpretations
for a set of variables of size n.
Requires that the variables be of
the form (mkVar v) where v ranges
exactly from 0 to (n-1).
-/
def mthInterpOf2toN (m n: ℕ) : var → bool :=
    -- for m >= 2^n, inter/row is all false
    if (m >= 2^n)
    then (λ v, ff) 
    else
    -- otherwise fill first n entries with
    -- i'th digits of m expressed in binary
    λ v : var, 
        match v with
        | (mkVar i) := 
            -- beyond n variables fill with false
            if i >= n then 
                ff 
            else 
            -- otherwise with correct digit/truth value
                (mrbn i m)
        end


/-
Generate a list of interpretations  
-/
def interps_helper : nat → nat → list (var → bool)
| 0 n := list.cons (mthInterpOf2toN 0 n) list.nil
| (nat.succ m') n := 
    list.cons 
        (mthInterpOf2toN (nat.succ m') n)
        (interps_helper m' n)

/-
return list of all interpretations for n variables
-/
def interps : ℕ → list (var → bool)
| nat.zero := []
| n := interps_helper (2^n-1) n

/-
return result of evaluating expr under each interp
-/
def interp_results (p : pExp) (n : ℕ) :=
    list.map 
        (λ (i : var → bool), pEval p i)
        (interps n)

#reduce interp_results (X ⇒ Y) 2


def first_n_true_inter (n : ℕ) : var → bool :=
λ v, 
    match v with
    | (var.mkVar n') := if n' < n then tt else ff
    end

def all_models (e : pExp) :=
    { m | isModel m e}


def sat_solve (e : pExp) : option (var → bool) :=
none

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


