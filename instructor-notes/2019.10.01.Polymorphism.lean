/-
A simple "boxed value" type. Think of
a value/term of this type as a box that
simply contains a value of another type.
In the first instace, the other type is ℕ.
-/

inductive boxed_nat : Type
| box_nat : nat → boxed_nat
open boxed_nat

def b1 := box_nat 3

def unbox_nat : boxed_nat → nat
| (box_nat n) := n

#eval unbox_nat b1

-- Exercise: implement a box_string type
-- Exercise: implement a box bool type


/-
Again, a problem of mostly repeated code
with a single point of variation: the type
of element held in a box.
-/

/-
Question: what's solution to multiplicity?
Answer: abstract variation to parameter.
Variation is in *type* of an argument.
Solution know as parametric polymorphism.
-/

-- Make the varying type a parameter!
-- We use Greek letters for type arg names
inductive boxed (α : Type) : Type
-- value of α is type of element to be boxed
| box : α → boxed
-- box takes *value* of type α, and boxes it

open boxed

/-
-/
def a : boxed nat := box 3
def a' := box 3      -- Lean infers a' type
def b := box "Hello" -- okay this is cool
def c := box ff      -- wow, this is cool!

/-
A polymorphic function has a type parameter.
-/
def unbox' (α : Type) : boxed α → α
| (box v) := v

/-
An equivalent way to write this definition.
We will prefer the former representation. It
is clearer and easier to read and write. 
-/
def unbox'' (α : Type) (b : boxed α) : α :=
match b with 
    | (box v) := v 
end

/-
While what we've got is pretty cool, using
it is a little burdensome, in that we have
to explicitly specify Type-valued arguments
when using the unbox function.
-/
#eval unbox' nat a
#eval unbox' string b
#eval unbox' bool c

/-
Lean expects that type argument, so the 
following won't work. The error message
says Lean is expecting an argument of type
"Sort". "Sort" in this context means Type.
We'll talk more about "Sort" later.
-/
#eval unbox a    -- Argument is explicit


/-
Now Lean *can* in fact figure out what the
value of the Type argument must be when it
has a boxed value in hand, such as "a" or 
"c" in the following examples.
-/
#eval unbox' _ a    -- Lean can infer α!
#eval unbox' _ c    -- Lean can infer α!

/-
If Lean can figure out what the value of 
the type argument is, then we should be
able not to give it explicitly
-/

-- Solution: implicit (type) arguments
def unbox {α : Type} : boxed α → α 
-- Use curly braces to indicate implicit arg
| (box v) := v

/-
Now you don't have to, and in you must not,
give a type value explicitly
-/
#eval unbox a
#eval unbox a'
#eval unbox b
#eval unbox c

/-
If we want to turn off implicit argument
inference and give type values explicitly,
we prefix the function application with @. 
-/

#eval @unbox nat a
#eval @unbox nat a'
#eval @unbox string b
#eval @unbox bool c



/-
EXERCISES
-/

/-
Define a polymorphic type, (moption α). This
type will have two constructors: one, "none"
and the other "some : α → option". Note that
you do not have to write α after option in 
the return type.
-/

inductive moption (α : Type) : Type
| none {} : moption
| some : α → moption

/-
Watch out, there is already an option
type in Lean, its namespace is opened,
and its some and none constructors are
already defined in the global namespace.
-/
#check option
#check some
#check none

/-
Be sure to use moption, moption.some,
and moption.none in work to follow.
-/

/-
The some constructor makes moption into 
a type almost exactly the same as box,
while the none constructor adds one more
value/term to this type. The "option α"
type in functional programming is usually
used as the return type of a function that
can return either a normal value (some α)
or an error (none). 
-/

/-
Write a polymorphic function, option_value,
that takes a value of type (option α), where
α is any type, along with a "default" value
of type α, and that returns as follows: if
the option is none, return the default value,
otherwise, if the option is (some v), return 
the normal value, v. Make the type argument 
implicit.
-/

def option_value {α : Type} : 
    moption α → α → α 
| moption.none d := d
-- without {} in the constructor definition
-- we'd have needed to say (moption.none α)
| (moption.some v) d := v

def o1 := moption.some 3
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


/-
Types and functions can be polymorphic in
more than one argument. Next week look at 
a polymorphic type the terms of which we 
will use to represent ordered pairs, as
they appear in ordinary high-school algebra.
-/

/-
First, let's see that we can define a type
to represent pairs of nats. We will use the
name "prod" to represent a type of pairs.
-/

inductive prod_nat_nat : Type
| pair : ℕ → ℕ → prod_nat_nat

def nn := prod_nat_nat.pair 2 3
#reduce nn

def fst_nat_nat : prod_nat_nat → nat
| (prod_nat_nat.pair x y) := x

def snd_nat_nat : prod_nat_nat → nat
| (prod_nat_nat.pair x y) := y

#reduce fst_nat_nat nn
#reduce snd_nat_nat nn

/-
You can see we're going to run right into 
the same problem of a multiplicity of prod
types, one for each type of pair (given by
a pair of types) that we want to represent.

The solution is to def a type, and its
associated functions, polymorphic in two
type arguments.
-/

inductive mprod (α β : Type) : Type
| pair : α → β → mprod

def fst (α β : Type) : mprod α β → α 
| (mprod.pair a b) := a

def snd (α β : Type) : mprod α β → β 
| (mprod.pair a b) := b

/-
Exercise: write a polymorphic swap
function that takes a pair and reverses
its elements.
-/

def swap (α β : Type) : mprod α β → mprod β α
| (mprod.pair a b) := mprod.pair b a


/-
Exercise: In earlier work, we defined mcompose to be a function that takes two
functions of type ℕ → ℕ and returns their composition. Here we'll give it again but
will call it compose_n_n_n to reflect the
fact that all three types involved are 
nat
-/

def mcompose_n_n_n : 
    (ℕ → ℕ) → (ℕ → ℕ) → (ℕ → ℕ) 
| g f := λ n, g ( f n)

/-
Generalize this function so that for
arbitrary types, α, β, and γ, it returns
compositions of functions of types β → γ 
and α → β. For example, if you wanted to
determine whether the length of a string
is even, you could first apply a function, 
f, of type string → ℕ to obtain the length
of the string, then, to the result, apply
a function of type ℕ → bool that returns
true if the given length is even. Use
implicit type arguments.
-/

def mcompose {α γ β : Type} : (β → γ) → (α → β) → (α → γ)
| g f := λ (n : α), g (f n)


/-
Define is_str_ev to be bound to a 
function that  returns true iff its 
argument's length is even. Use the
mcompose function to compute the
function rather than programming 
it explicitly. Note: string.length
is the function in Lean that returns
the length of a string; and you can
use the mod operator, %, to determine
if a natural number is even or not.
Please define the type of is_str_ev
explicitly to be string → bool.
Test your function using eval.
-/
def is_str_ev : string → bool := 
    mcompose 
    (λ n, n % 2 = 0)
    (λ s, string.length s)

#eval is_str_ev "Hello Th"

/-
What is the type of a polymorphic function?
-/

#check mcompose
#check @mcompose

/-
The Π is an expression that gives names to
arguments earlier in an argument list, the
values of which can then be used later in
the same argument list! If we just wrote
Type → Type → Type → ??? → ??? → ???, we'd 
have no way to refer to the values of the
first three arguments. Lean assigns the
names ?M_3, ?M_2, and ?M_1 when the type
parameters are implicit, and uses Π to 
bind our names to these parameters when
we turn off implicit typing, in which case
the real substance of the function type is
made clear.
-/

/-
Homework: 

#1. In a file called moption.lean,
define a polymorphic option abstract
data type. In a separate file called
moption_verify.lean import the first
file and write a set of definitions
that show how to use the data type
and that test its functions.

- fst
- snd
- swap

#2. 
In a file called mlist.lean,
define a polymorphic list abstract
data type. Call your data type mlist. 
Give it two constructors called nil
and cons. Do not use Lean's list data
type in this assignment.

- prepend: given (a : α) and (l : mlist α) return (cons a l)
- mhead: given (l : mlist α) return option containing head or none
- mtail: given (l : mlist α) return option containing tail or none
- mlength: given (l : mlist α), return length of l as a ℕ 
- mmap: given (f : α → β) and (l : list α) return list β
- mfold: given (f : α → α → α) (id : α) and (l : list α) implement fold

In a separate file, called mlist_verify.lean, write
a set of test cases, details TBD.

#2. Do the same for a polymorphic mprod/pair abstract
data type. You can use the materials developed here
for this purpose.
-/