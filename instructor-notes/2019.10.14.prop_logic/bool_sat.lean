import .prop_logic 

open prop_logic 

open prop_logic.var
open prop_logic.unOp
open prop_logic.binOp
open prop_logic.pExp


def X : pExp:= varExp (mkVar 0)
def Y : pExp := varExp (mkVar 1)
def Z : pExp := varExp (mkVar 2)
def W : pExp := varExp (mkVar 3)

def anExp : pExp := (X ∧ Y) ∨ Z


/-
    *****************************
    *** SATISFIABILITY solver ***
    *****************************
-/

-- m'th bit from right in binary rep of n
def mrbn: ℕ → ℕ → bool 
| 0 n := n % 2 = 1
| (nat.succ m') n := mrbn m' (n/2) 

#eval mrbn 2 4

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

#eval interp_results ((X ∧ Y) ↔ (Y ∧ X)) 2


