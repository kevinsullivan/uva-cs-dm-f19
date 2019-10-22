import ..src.moption

/-
Watch out, there is already an option
type in Lean, its namespace is opened,
and its some and none constructors are
already defined in the global namespace.
-/
#check option
#check some
#check none

def o1 : moption nat := moption.some 3
def o2 := moption.some "Hi there"
def o3 := moption.some tt

/-
We have to turn off implicit arguments
when using the none constructor, as there
are no other arguments from which Lean
can infer the type argument's value.
-/
def e1 := @moption.none nat
def e2 := @moption.none string
def e3 := @moption.none bool

-- return boxed value
#eval option_value o1 0
#eval option_value o2 ""
#eval option_value o3 ff

-- or none if there isn't one
#eval option_value e1 0
#eval option_value e2 ""
#eval option_value e3 ff
