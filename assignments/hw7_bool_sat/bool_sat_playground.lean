import .prop_logic 
import .bool_sat

open prop_logic 
open prop_logic.var
open prop_logic.pExp

/-
Play around, i.e., experiment with,
and practicing using, the functions
defined in bool_sat.lean. Here are
a few definitions to get you started.
-/

/-
We define a few variables to use
in the rest of this assignment.
-/
def P : pExp:= varExp (mkVar 0)
def Q: pExp := varExp (mkVar 1)
def R : pExp := varExp (mkVar 2)
def max_var_index := 2
def num_vars := max_var_index + 1

-- Practice below!

