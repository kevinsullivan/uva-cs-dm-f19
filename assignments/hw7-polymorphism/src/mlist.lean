import ..src.moption

open moption_namespace

namespace mlist_namespace

-- type args implicit within this definition
inductive mlist (α : Type): Type 
| nil {} : mlist  
| cons : α → mlist → mlist

-- You may open mlist, as list isn't open

open mlist

def prepend {α : Type} : α → mlist α → mlist α 
| a l := cons a l

-- Use moption.___, as option is open
def mhead {α : Type} : mlist α → moption α
| nil := moption.none
| (cons h t) := moption.some h

def mtail {α : Type} : mlist α → moption (mlist α)
| nil := moption.none
| (cons h t) := moption.some t

def mlength {α : Type} : mlist α → ℕ
| nil := 0
| (cons h t) := 1 + mlength t

def mappend {α : Type} : mlist α → mlist α → mlist α 
| nil l := l
| (cons h t) l := cons h (mappend t l)

def mmap {α β : Type} : (α → β) → mlist α → mlist β
| f nil := nil
| f (cons h t) := cons (f h) (mmap f t)

def mfold {α β : Type} : (α → β → β) → β → mlist α → β 
| op id nil := id 
| op id (cons h t) := op h (mfold op id t)

end mlist_namespace
