namespace myoption

inductive moption (α : Type) : Type
| some (a : α) : moption
| none : moption

#check moption.some 4

end myoption