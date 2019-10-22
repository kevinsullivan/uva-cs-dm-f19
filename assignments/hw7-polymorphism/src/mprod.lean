/-
Define a polymorphic type, mprod, 
with two type parameters, α and β,
with one constructor, pair, that
takes two values, one of type α
and one of type β. We will interpret
a given term, (pair a b), of type
(mprod α β), as an ordered pair,
(a, b), of the kind discussed in
ordinary high-school algebra. We
give you a start on the answer.
Fill in the underscores.
-/

-- Answer here

inductive mprod (α β : Type) : _
| pair : α → β → mprod
-- Do not open the mprod namespace

/-
Define a polymorphic function, fst,
that has two type parameters, α and
β, takes a pair of type mprod α β,
and that returns the first value in
the pair. Make the type arguments
implicit (use curly braces instead
of parentheses).
-/


def fst {α β : Type} : mprod α β → α 
| (mprod.pair a b) := a

/-
Define a corresponding function, snd,
that returns the second value in any
given pair (with implicit arguments).
-/

def snd {α β : Type} : mprod α β → β 
| (mprod.pair a b) := b


/-
Define a polymorphic swap function
that takes a pair of type mprod α β 
and that return a pair with the values
in the opposite order. Make the type
arguments implicit. So, for example,
swap (3, tt) should return (tt, 3).
-/

def swap {α β : Type} : mprod α β → mprod β α
| (mprod.pair a b) := mprod.pair b a
