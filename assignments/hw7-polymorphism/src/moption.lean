namespace moption_namespace

inductive moption (α : Type) : Type
| none {} : moption
| some : α → moption
-- {} makes the argument to none implicit

-- Do not open the moption namespace

/-
This option_value function is like the
unbox function we defined for our boxed
type. The challenge is to return a value
when the option "box" is empty (none).
We thus provide a second argument to 
this function (in addition to an option
value), which the function uses as the
"default" return value if and only if
the option value is none. We ignore the
default value when the option is of the
form (some v).
-/
def option_value {α : Type} : moption α → α → α 
| moption.none default := default
| (moption.some v) _ := v

#check eq

end moption_namespace
