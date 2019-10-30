
--import .prop_logic 
import .prop_logic

open prop_logic
open prop_logic.var
open prop_logic.unOp
open prop_logic.binOp
open prop_logic.pExp


/-
Define a few propositional variables.
-/

def P := varExp (mkVar 0)
def Q := varExp (mkVar 1)
def R := varExp (mkVar 2)

/-
Which of the following propositions are valid?
And which are logical fallacies (i.e., not valid)?
-/
def true_intro : pExp := pTrue
def false_elim := pFalse ⇒ P
def and_intro := P ⇒ Q ⇒ P ∧ Q
def and_elim_left := P ∧ Q ⇒ P
def and_elim_right := P ∧ Q ⇒ Q
def or_intro_left := P ⇒ (P ∨ Q)
def or_intro_right := Q ⇒ (P ∨ Q)
def or_elim := (P ∨ Q) ⇒ (P ⇒ R) ⇒ (Q ⇒ R) ⇒ R
def iff_intro :=   (P ⇒ Q) ⇒ (Q ⇒ P) ⇒ (P ↔ Q)
def iff_intro' := ((P ⇒ Q) ∧ (Q ⇒ P)) ⇒ (P ↔ Q)
def iff_elim_left := (P ↔ Q) ⇒ (P ⇒ Q)
def iff_elim_right := (P ↔ Q) ⇒ (Q ⇒ P)
def arrow_elim := (P ⇒ Q) ⇒ P ⇒ Q
def resolution := (P ∨ Q) ⇒ (¬ Q ∨ R) ⇒ (P ∨ R)
def unit_resolution := (P ∨ Q) ⇒ (¬ Q) ⇒ P
def syllogism := (P ⇒ Q) ⇒ (Q ⇒ R) ⇒ (P ⇒ R)
def modus_tollens := (P ⇒ Q) ⇒ ¬ Q ⇒ ¬ P
def neg_elim := ¬ ¬ P ⇒ P
def excluded_middle := P ∨ ¬ P
def neg_intro := (P ⇒ pFalse) ⇒ ¬ P
def affirm_consequence := (P ⇒ Q) ⇒ Q ⇒ P
def affirm_disjunct := (P ∨ Q) ⇒ P ⇒ ¬ Q
def deny_antecedent := (P ⇒ Q) ⇒ (¬ P ⇒ ¬ Q)