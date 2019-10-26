import .prop_logic 

open prop_logic 

open prop_logic.var
open prop_logic.unOp
open prop_logic.binOp
open prop_logic.pExp


/-
*** SATISFIABILITY solver ***

This module implements a model finder.
It works by generating the 2^n possible
interpretations of a given propositional
logic formula, where n is the number of
distinct variables in the formula, and
by then evaluating the formula under 
each of the interpretations to produce
a list of Boolean truth values. True
entries correspond to models of the
given formula.

The insight on which the design of
the model finder is based is that 
in a truth table for an expression
based on a set of n variables, with
are 2^n rows (each corresponding to
an interpretation), and the truth 
table entry for the k'th variable 
in the m'th row is given by the k'th
bit in the binary representation of 
the number, m.
-/

/-
Given (m n : nat), return m'th bit from 
the right in binary representation of n.
Formerly called mrbn. However, the mrbn
function returned a bool. This function 
just returns 0 or 1 of type nat. We then
provide the following function to turn
such a nat into a bool in the usual way,
with 0 mapping to ff and 1 (or any other
nat) mapping to tt.
-/
def mth_bit_from_right_in_n: ℕ → ℕ → ℕ  
| 0 n := n % 2
| (nat.succ m') n := 
    mth_bit_from_right_in_n m' (n/2) 

/-
Convert bit value 0 or 1 (of type nat)
to corresponding Boolean value.
-/
def bit_to_bool : ℕ → bool
| 0 := ff
| _ := tt

/-
Given (m n : ℕ) return the m'th
interpretation in an enumeration
of the 2^n interpretations given
n variables. 

Recall that in our formalization
of the semantics of propositional
logic, an interpretation is given
as a function from var to bool,
and there is an infinite number
of values of type var.

This function just assigns the
"default" value ff to each variable
of the form (mkVar k) where k >= n,
and returns the "all false"
intepretation function when
m >= 2^n. Otherwise it returns
an interpretation where the first
n truth values are given by the
n bits in the binary expansion
of m. 
-/
def mth_interp_n_vars (m n: ℕ) : var → bool :=
if (m >= 2^n)
    then λ v, ff
else
    λ v : var, 
    match v with
    | (mkVar i) := 
        if i >= n then ff 
        else bit_to_bool 
                (mth_bit_from_right_in_n i m)
    end


/-
This is a helper function for the primary
function that follows. The primary function
which is non-recursive and takes an argument,
n, calls this recursive function with m=2^n
and n to build a list of 2^n interpretations
for n variables.

Given arguments (m : nat) being the number 
of interps to  generate and (n : nat), the
number of variables, return a list of m 
interpretations. In practice this function 
is only called by the primary function and
is called with m = 2^n. Using recursion it 
then "loops" m=2^n times to build a list of
the required 2^n interpretations for a case
in which there are n relevant variables.
-/
def interps_helper : nat → nat → list (var → bool)
| 0 n := list.cons (mth_interp_n_vars 0 n) list.nil
| (nat.succ m') n := 
    list.cons 
        (mth_interp_n_vars (nat.succ m') n)
        (interps_helper m' n)

/-
Primary function: return list of all 
possible interpretations for n variables
-/
def interps_for_n_vars : ℕ → list (var → bool)
| nat.zero := []
| n := interps_helper (2^n-1) n

/-
Return list of Boolean results of evaluating 
a given propositional logic expression, p,
under each of its possible interpretations.
That is, return a list of the truth table
"result" for the given expression under 
each of its possible
The second argument, n, indicates the highest
"index" of any variable in the expression, p.

Precondition: if the variable expressions in
p are (varExp (mkvar 0)), varExp (mkVar 1), and
varExp (mkvar 3), for example, then the value
of the second argument, n, should be set to 4.
The resulting truth table will then contain 16
rows/interpretations, in which (mkvar 2) will
also be given values. These values won't affect
how p is evaluated, because that variable does
not appear in p, but the variable nevertheless
has to appear in the truth table for this code
to work. If you "number" you var objects from 
0 to n-1, using (mkVar 0), ..., (mkVar n-1),
then use n as the value of the second argument.
-/
def truth_table_results (p : pExp) (n : ℕ) :=
list.map 
    (λ (i : var → bool), pEval p i)
    (interps_for_n_vars n)

