/-
The identity function for any type.
-/

namespace review 

def id' {α : Type} : α → α := 
    λ (a : α), a

def id {α : Type} (a : α) : α := a

#eval id 3
#eval id tt
#eval id "I love type arguments!"

inductive boxed (α : Type) : Type
| box : α → boxed 

open boxed

def unbox (α : Type) : boxed α → α 
| (box a) := a

/-
A polymorphic ordered pair type
-/

inductive prod (α β : Type) : Type
| pair (a : α) (b : β) : prod

def p1 : prod bool nat := prod.pair ff 3

def fst {α β : Type} : prod α β → α 
| (prod.pair a b) := a

def snd {α β : Type} : prod α β → β  
| (prod.pair a b) := b

def swap {α β : Type}  : prod α β → prod β α 
| (prod.pair a b) := prod.pair b a

#eval fst p1
#eval snd p1
#reduce swap p1

#check list

inductive mlist (α : Type) : Type
| nil : mlist
| cons (h : α) (t : mlist) : mlist

end review