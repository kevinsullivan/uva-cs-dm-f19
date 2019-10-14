
namespace review 

/-
The identity function for any type:
a *polymorphic* identity function.

Key points: type parameters (i.e.,
polymorphism); type inference; and
implicit type arguments.
-/

def id (α : Type) (a : α) : α := a

/-
Examples of its use. Note how we
have to specific type argument
values explicitly--bool string, 
nat--even though they clearly can
be inferred from the value of the
second argument.
-/
#eval id bool tt
#eval id string "I love polym!"
#eval id nat 4

#check id

/-
We can ask Lean to infer the value
of the first, type, parameter and to
make it implicit, so that we don't
have to provide it explicitly when
we use the id' function. Here we also
use a "by cases" rather than C-style
presentation of this function.
-/

def id' {α : Type} : α → α 
| a := a

/-
Sometimes we want to turn off implicit
inference of arguments. We do that by
prefixing an expression that uses implicit
arguments with @.
-/
#check (@id' nat)
#eval @id' bool tt

/-
Examples with implicit type arguments.
-/
#eval id' "I love polym!"
#eval id' 4

#check id'

/-
Boxed again: A NON-polymorphic version
of a "boxed value" data type -- this one
is dedicated to "boxing up" nat values.
-/

inductive boxed_nat : Type
| box_nat : ℕ → boxed_nat

inductive boxed_nat' : Type
| box_nat (n : ℕ) : boxed_nat'

open boxed_nat

def unbox_nat : boxed_nat → ℕ 
| (box_nat v) := v

#eval unbox_nat (box_nat 4)

/-
Here's a corresponding polymorphic
version, in which we've *abstracted* 
from nat to "any type" as indicated
by the type argument, α.
-/

inductive boxed (α : Type) : Type
| box : α → boxed

-- Another way to write the same
-- "box" constructor, in more of
-- a C style.

inductive boxed' (α : Type) : Type
| box (n : α) : boxed'

open boxed

-- A polymorphic unbox function taking
-- its type argument implicitly.

def unbox {α : Type} : boxed α  → α  
| (box v) := v

#eval unbox (box 4)
#eval unbox (box tt)
#eval unbox (box "I love this stuff!")

/-
A polymorphic "product type", prod. A product
type is a type whose values are ordered pairs.
Here the types of the first and second elements
of such a pair are given by the values of two
type arguments, α and β respectively. The pair
constructor takes a value of type α and one of
type β and yeilds the term (pair a b), whic we 
will interpret as representing the ordered pair,
(a, b), a concept that should be familiar from
basic high school algebra.
-/



inductive prod (α β : Type) : Type
| pair (a : α) (b : β) : prod

/-
Functions that take a pair (or a longer
"tuple") and that return one of its
component values is called a projection
function. Here we define two polymorphic
projection functions for ordered pairs:
fst returns the first element of a given
pair, and snd returns the second one.
-/

def fst {α β : Type} : prod α β → α 
| (prod.pair a b) := a

def snd {α β : Type} : prod α β → β 
| (prod.pair a b) := b

/-
This function swaps the values in a pair.
Take note of the type of this polymorphic
function.
-/
def swap {α β : Type} : prod α β → prod β α 
| (prod.pair a b) := prod.pair b a

/-
Examples.
-/
def p1 := prod.pair 3 tt
#eval fst p1
#eval snd p1
#reduce swap p1
































def id' {α : Type} : α → α := 
    λ (a : α), a

def id {α : Type} (a : α) : α := a

#eval id 3
#eval id tt
#eval id "I love type arguments!"

/-
Reviewing simple polymorphic types
-/

inductive boxed (α : Type) : Type
| box : α → boxed 

open boxed

def unbox (α : Type) : boxed α → α 
| (box a) := a

/-
A more interesting polymorphic type.
The type, prod, of ordered pairs. 
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

/-
A polymorphic list type!
-/

inductive mlist (α : Type) : Type
| nil : mlist
| cons (h : α) (t : mlist) : mlist

end review