-- Namespaces

-- Here is the global namespace

-- first namespace nested within global
namespace cs
def x := 1
#check x
#eval x
end cs

-- second namespace 
namespace oc
def x := "Hi!"
#check x
#eval x
end oc

-- namespaces are closed by default
#eval cs.x
#eval oc.x

#eval x -- x not visible in global ns

open cs -- names in cs visible in global 
#eval x

open oc -- names in oc now also visible
#eval x -- but x now ambiguous in global
#eval cs.x  -- must disambiguate
#eval oc.x  -- with namespace qualifier


-- Ambiguity even if values are same
namespace n1
def q := 1
end n1

namespace n2
def q := 1
end n2

open n1
open n2

#check q    -- ambiguous

/- END OF NAMESPACE TOPIC -/

/- ON TO TYPES -/

/-
So far we have seen data types and
function types. You can think of these
as *computational* types. Later on we
will introduce *logical* types.

Types are also values and so they,
too, have types. The type of any
computation type is "Type".
-/

-- the type of a data type is Type
#check 1
#check ℕ 
#check bool
#check string

-- the type of a function type is Type
#check nat → nat
#check string → nat
#check nat → nat → bool


-- Big idea: we can define new data types
-- The type of such a type will be Type
inductive day : Type
| sun : day
| mon : day 
| tue -- Lean infers types
| wed 
| thu 
| fri 
| sat 

#check day.mon
/-
The constructor names of a type are
defined in a namespace with the same
name as the type.
-/
open day

#check day
#check sun


-- next_day function (by cases)
def next_day : day → day 
| sun := mon
| mon := tue
| tue := wed
| wed := thu
| thu := fri
| fri := sat 
| sat := sun

-- evaluate an application term
#reduce next_day mon

-- is_weekend function by cases
def is_weekend : day → bool 
| sun := tt
| mon := ff
| tue := ff
| wed := ff
| thu := ff
| fri := ff 
| sat := tt

-- evaluate an application term
#reduce is_weekend mon

/-
How can we define a type with an
infinite number of values, such as
nat? The key is to define constructors
that build larger values of a type from
given smaller values. One ends up with
an *inductively defined type*.
-/

inductive my_nat : Type
| zero : my_nat 
| succ : my_nat → my_nat 

open my_nat 

#reduce zero
#reduce succ zero
#reduce succ (succ zero)

def is_zero : my_nat → bool
| zero := tt
| _ := ff

#reduce is_zero zero
#reduce is_zero (succ ( succ zero))