/-
CS 2102, Fall 2019, Sullivan sections.
Inductive type definitions, recursive
functions, and higher-order functions.
-/

/-
Problem #1. We give you a simple "natural 
number arithmetic abstract data type based
on our own mnat type for representing the 
natural numbers. You are to extend it by 
adding definitions of several operations
(functions). 

The first is a boolean "less than" 
operator. It will take two natural 
numbers and return true (tt) if and only 
if the first is less than the second 
(otherwise it will return false). 

The second function will implement mnat
multiplication. It will use recursion and
the given definition of mnat addition.

The third function will implement the
factorial function using the mnat type.
The factorial of zero is one and the 
factorial of any number n = 1 + n' is
n times the factorial of n'. 
-/

-- Here's the logic we've already covered.

inductive mnat : Type
| zero
| succ : mnat → mnat

open mnat 

-- an increment function
-- takes mnat, returns one greater nmat
def inc : mnat → mnat :=
    λ n : mnat, succ n

-- alternative syntax (c-style)
def inc' (n : mnat) : mnat :=
    succ n

-- is_zero predicate
-- return tt iff and only if mnat is zero 
def is_zero : mnat → bool
| zero := tt
| _ := ff

-- predecessor
-- returns zero when mnat is zero
-- else returns one less than given mnat
def pred : mnat → mnat 
| zero := zero
| (succ m) := m

-- equality predicate
-- tt if given mnats are equal else ff
def eq_mnat : mnat → mnat → bool
| zero zero := tt 
| zero (succ m) := ff
| (succ m) zero := ff
| (succ m) (succ n) := eq_mnat m n

-- mnat addition
-- by cases on first argument
-- zero + any m returns m
-- (1 + n') + m returns 1 + (m' + n)
-- understand why the recursion terminates
def add_mnat : mnat → mnat → mnat
| zero m := m
| (succ n') m := succ (add_mnat n' m)


/- [10 points]
#1A. Implement an mnat "less than" 
predicate by completing the following 
definition. Fill in the placeholders.
-/

def lt_mnat : mnat → mnat → bool
| zero zero := ff
| zero _ := tt
| (succ n') zero := ff
| (succ n') (succ m') := lt_mnat n' m'

-- We give you shorthand names for a few mnats
def mzero := zero
def mone := succ zero
def mtwo := succ (succ zero)
def mthree := succ (succ (succ zero))
def mfour := succ mthree

-- When you succeed, the following tests
-- should all give the right answers.
#reduce lt_mnat mzero mzero
#reduce lt_mnat mzero mtwo
#reduce lt_mnat mtwo mtwo
#reduce lt_mnat mtwo zero
#reduce lt_mnat mtwo mthree
#reduce lt_mnat mthree mtwo 


/- [10 points]
#1B. Implement an mnat multiplication
function by completing the following
definition. Hint: use the distributive
law. What is (1 + n') * m? Also be sure
you see why the recursion terminates in 
all cases.
-/

-- Answer
def mult_mnat : mnat → mnat → mnat
| zero _ := zero
| (succ n') m := add_mnat m (mult_mnat n' m)

-- When you succeed you should get
-- the right answers for these tests
#reduce mult_mnat mzero mzero
#reduce mult_mnat mzero mthree
#reduce mult_mnat mthree mzero
#reduce mult_mnat mtwo mthree
#reduce mult_mnat mthree mtwo
#reduce mult_mnat mthree mthree


/- [10 points]
#1C. Implement the factorial function
using the mnat type. Call your function
fac_mnat. Give a definition by cases using
recursion, in the style of the preceding
examples.
-/

-- Your code here

def fac_mnat : mnat → mnat
| zero := (succ zero)
| (succ n') := mult_mnat (succ n') (fac_mnat n')

-- Add test cases for zero, one, and
-- some larger argument values and check
-- that you're getting the right answers.

-- Here
-- Test
#reduce fac_mnat mzero
#reduce fac_mnat mone
#reduce fac_mnat mthree


/-
#2. Inductive data type definitions.

For this problem, you will extend a 
very simple "list of natural numbers"
abstract data type. The technical term
for a list is a "sequence". You will 
first read understand a list_nat data 
type and you will then define several
functions that operate on values of
this type. As you work through these
problems, note their similarity to
comparable functions involving the
natural numbers (such as is_zero,
succ, pred, and add).
-/

/-
The following inductive definition
defines a set of terms. The base case is
nil, representing an empty list of mnat.
The cons constructor on the other hand
takes an mnat (let's call it h) and any
list of mnats (call it t) and returns the
term, (cons h t), which we interpret as a
one-longer list with h at its "head" and
the one-smaller list, l, as its "tail"). 
-/
inductive list_mnat : Type
| nil
| cons : mnat → list_mnat → list_mnat

open list_mnat 

-- Here are two list definitions using
-- our new data type

-- representation of an empty list
def empty_list := nil

-- representation of the list [1, 2, 3]
def one_two_three := 
    cons 
        mone 
        (cons 
            mtwo 
            (cons 
                mthree
                nil
            )
        )

/-
2A. [10 points]

Define three_four to represent the
list [3, 4].
-/

-- Here

def three_four := 
    cons mthree 
    (
        cons 
            mfour 
            nil
    )
-- or equivalent

/-
#2B. [10 points]

Implement a predicate function,
is_empty, that takes a list_mnat and
returns true if an only if it's empty,
otherwise false. Remember once again
that a "predicate" function is one
that returns a Boolean true or false
value depending on whether the argument
to which it is applied has a specified
property or not. Here the property is
that of being an empty list, or not.
-/

-- Your answer here

def is_empty : list_mnat → bool
| nil := tt
| _ := ff


/-
#2C. [10 points]

Implement a prepend_mnat function
that takes an mnat, h, and a list_mnat,
t, and that returns a new list with h
as the value at the head of the list
and t as the "rest" of the new list (its
"tail").
-/

-- Your answer here

def prepend_mnat : mnat → list_mnat → list_mnat
| h t := cons h t


/-
#2D. [10 points]

Implement a "length_mnat" function
that takes any list_mnat and returns its
length represented as a value of type mnat. 
The length of the empty list is zero and 
the length of a non-empty list, (cons h t),
is one more than the length of t.
-/

def length_mnat : list_mnat → mnat
| nil := zero
| (cons h t) := succ (length_mnat t)


/-
2F. [Extra Credit]

Implement an append_mnat function. 
It takes two list_mnat values and returns
a new one, which is the first appended
to (and followed by) the second. So, for
example, the list [1, 2] appended to the
list [3, 4, 5] should return the list,
[1, 2, 3, 4, 5]. Of course you won't be
using this nice list notation, just the
constructors we've defined.

To understand how to solve this problem,
start by really thoroughly seeing how the
addition function for mnats works. It 
uses recursion on the *first* of the two
arguments. If the first argument is zero,
it returns the second argument without 
change. Similarly, here, if the first list
is nil, the result is the second list. If
the first list is not nil, then it must
be of the form (cons h t). In this case,
the head of the new list will be h. What
will be the tail of the new list?
-/

-- Your answer here

def append_mnat : list_mnat → list_mnat → list_mnat
| nil l := l
| (cons h t) l := cons h (append_mnat t l)


/-
Add tests where the first list is nil and
not nil, and make sure you're getting the
right answers.
-/ 

#reduce append_mnat one_two_three three_four

/-
#3. Higher-Order Functions

Lean's library-provided polymorphic list type
is implemented in essentially the same way as
the list_mnat type you used in the preceding
questions. The main difference is that the
type of elements in a Lean list is given as 
a parameter to the "list" type. We covered 
the use of Lean's (polymorphic) list type
in class. Review your notes if necessary.
-/

/-
3A. [10 points] Provide an implementatation of
a function, map_pred. This function will take
as its arguments (1) any predicate function of
type ℕ → bool, (2) any list of natural numbers
(of type "list nat"). It will then return a new
list in which each ℕ value in the given list is
replaced by true (tt) if the predicate returns
true for that value, and otherwise by false (ff).

For example, if the predicate function returns
true if and only if its argument is zero, then
applying map to this function and to the list
[0,1,2,0,1,0] must return [tt,ff,ff,tt,ff,tt].


Test your code by using #eval or #reduce to evaluate
an expression in which map_pred is applied to 
such an "is_zero" predicate function and to the
list 0,1,2,0,1,0]. Express the predicate function
as a lambda abstraction within the #eval command.

NOTE: You will have to use list.nil and list.cons
to refer to the nil and cons constructors of the
library-provided list data type, as you already
have definitions for list and cons in the current
namespace.
-/

-- Answer here

def map_pred : (ℕ → bool) → list nat → list bool
| f list.nil := list.nil
| f (list.cons h t) := list.cons (f h) (map_pred f t)

#eval map_pred (λ n, n = 0) [0,1,2,3,0,5]

/-
3B. [5points] Implement a function, reduce_or, 
that takes as its argument a list of Boolean values 
and that reduces the list to a single Boolean value: 
tt if there is at least one true value in the list,
otherwise ff. Note: the Lean libraries provide the
function "bor" to compute "b1 or b2", where b1 and
b2 are Booleans. We recommend that you include
tests of your solution.
-/

-- example
#reduce bor tt tt

-- Answer here

def reduce_or : list bool → bool
| list.nil := ff
| (list.cons h t) := bor h (reduce_or t)

/-
3C. [5 points] Implement a function, reduce_and,
that takes as its argument a list of Boolean values 
and that reduces the list to a single Boolean value: 
tt if every value in the list is true, otherwise ff.
-/

-- Note: band implements the Boolean "and" function
#reduce band tt tt

-- Answer here

def reduce_and : list bool → bool
| list.nil := tt
| (list.cons h t) := band h (reduce_and t)

#reduce reduce_and list.nil
#reduce reduce_and [tt,tt,ff]

/-
3D. [10 points] Define a function, all_zero, that 
takes a list of nat values and returns true if and 
only if they are all zero. Express your answer using 
map and reduce functions that you have previously
defined above. Again we recommend that you test your 
solution.
-/

-- Answer here

def all_zero : list nat → bool
| list.nil := tt
| l := 
    reduce_and
    (
        map_pred (λ n, n = 0) l
    ) 

-- some tests
#reduce all_zero []
#reduce all_zero [0,0,0,0]
#reduce all_zero [1,0,0,0]
#reduce all_zero [0,1,0,0]
#reduce all_zero [1,0,0,1]


/-
This is the end of the homework. Please 
be sure to save your file before uploading
then check that you uploaded correctly. We
cannot accept work submitted incorrectly
or late, so take a minute to be sure you
got it right. Thank you!
-/
