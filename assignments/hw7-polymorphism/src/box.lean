inductive boxed (α : Type) : Type
| box : α → boxed

open boxed

def unbox {α : Type} : boxed α → α 
| (box v) := v

