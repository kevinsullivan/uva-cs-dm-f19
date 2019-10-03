namespace mlist

open list   -- Lean-provided data type

/-
Lists in Lean are "polymorphic." They
can contain elements of any specified
type. Your homework is to implement lists of natural numbers in particular. 
Soon you'll see how to make the type of
list elements into a parameter/argument.
To help with your homework, let's look
at lists as provided by Lean's library.
-/

/-
Inductive definition: A list is either 
empty or it is constucted (thus "cons")
from an element and a one-smaller list.
-/

/-
We represent an empty list by a term, nil.
-/
def e : list nat := nil
#check e
#eval e

/-
We represent a non-empty list by a term,
cons h t, where h is the element at the
"head" of the list and "t", the tail of
the overall list, is the one-smaller list
that follows the head. It in turn can be
(a term representing) the empty list or 
a non-empty list. 
-/

-- The list, [1]
def l1 : list nat := 
    cons 
        1   -- head element
        nil -- tail list

#eval l1

-- The list, [1, 2]
def l2 : list nat :=
    cons
        1
        (
            cons 
                2
                e
        )

def l3 : list nat :=
    cons
        1
        (
            cons 
                2
                (
                    cons
                        3
                        nil
                )
        )

def l3' : list nat :=
    cons 1 ( cons 2 ( cons 3 nil ) )
 

-- The list, [1, 2, 3]

#eval l3 -- note use of nice notation!

def my_list : list string :=
    cons 
        "I"
        (
            cons
                "love"
                (
                    cons
                        "DM"
                        (nil)
                )
        )

#eval my_list -- note nice notation


def my_list' : list string :=
    ["I", "love", "DM"]

-- Nested lists, response to question
-- represent [ [1,2], [3,4], [0,10] ]
-- notice the *type* of this list
def nested_list : list (list nat) :=
cons
    (

    )  -- [1,2]
    (
        cons
        (_) -- [3,4]
        (
            cons 
                (_) -- [0,10]
                nil
        )
    )
-- you can (and should) fill in _s

#check e
#eval e

#check l3
#eval l3

-- Lean supports list notation!
def l4 : list nat := [1, 2, 3, 4]
#check l4
#eval l4


/-
OK, now that we've seen how to use nil
and cons terms to represent lists, it's
time to define functions that operate on
lists represented by such terms. 
-/

-- A function to prepend nat h to list t

def prepend : nat → list nat → list nat
| h t := cons h t

#eval prepend 1 [2, 3, 4]


/-
Head takes a value of type list nat and
returns the nat head of the list if it 
is not empty otherwise it returns zero. 
-/


def mhead : list nat → nat
| [] := 0
| (cons h t) := h

#eval mhead []
#eval mhead [1, 2, 3]

def mtail : list nat → list nat 
| [] := []
| (cons h t) := t

#eval mtail []
#eval mtail [1, 2, 3]


-- return length of list
def mlength : list nat → nat
| [] := 0
| (cons _ t) := 1 + (mlength t)



#eval mlength []
#eval mlength l2
-- mlength [1 , 2]
-- 1 + (mlength [1])
-- 1 + (1 + (mlength []))
-- 1 + (1 + 0)
-- 1 + 1
-- 2 -- the final result

#eval mlength l4
/-
mlength [1, 2, 3, 4]
1 + (mlength [2, 3, 4])
1 + (1 + mlength [3, 4])
1 + (1 + (1 + mlength [4]))
1 + (1 + (1 + (1 + mlength [])))
1 + (1 + (1 + (1 + 0)))
1 + (1 + (1 + 1))
1 + (1 + 2)
1 + 3
4 -- the final result
-/



/-
After review of preceding,
START 9/26/2019 From Here
-/

/-
Warmup exercise: write countdown function.
Given a natural number, n, return a list of
natural numbers, [n, n-1, ..., 0].
-/

open nat

def countdown : ℕ → list nat
| 0 := [0]
| (succ n') := cons (succ n') (countdown n')

#eval countdown 10



/-
Exercise: write fib function. The key new element in
this definition is that it has two base cases instead
of one, and the third, recursive, case uses a more
complex form of pattern matching. 
-/


def fib : ℕ → ℕ 
| nat.zero := nat.zero
| (nat.succ nat.zero) := (nat.succ nat.zero)
| (nat.succ (nat.succ n')) := (fib n') + (fib (nat.succ n'))

/-
We can clean up this definition using Lean's built-in
machanisms for writing natural number values. The
following logic is absolutely equivant to the preceding
version.
-/

def fib' : ℕ → ℕ 
| 0 := 0
| 1 := 1
| (n' + 2) := (fib n') + (fib (n' + 1))

#eval fib 10
#eval fib' 10


/-
Now a function that takes a list (of nats) and
that returns a new list, like the first, except
that every element in the first list is doubled
in the second list.

Study the second case especially carefully. On
the left of the :=, we take apart the argument
list into a head, h, and a tail, t. On the right,
we use cons to build a new list: one with 2*t at
its head and with a doubled version of t as its
tail. The doubled version of t is returned by the
recusive application of mdouble to t.
-/
def mdouble : list ℕ → list ℕ  
| [] := []
| (cons h t) := cons (h*2) (mdouble t)

#eval mdouble []
#eval mdouble l4


/-
We don't want to have to write multiple
functions like mdouble that differ only
in the function applied to h. The solution
is to make that function a parameter. This
generalizes the function to one that can
transform any list of natural numbers 
into a corresponding list where the 
new list elements are computed by 
applying the function to the elements
of the original list.
-/
def mmap : (ℕ → ℕ) → list ℕ → list ℕ 
| f [] := []
| f (cons h t) := cons (f h) (mmap f t)

#eval mmap nat.succ [1,2,3,4]   -- add one to each element
#eval mmap (λ (n : ℕ), n*n) [1,2,3,4] -- square each element


/-
A "reduce" function takes a list as an argument and
reduces it to a single value by applying an operation
between elements in the list. If the operation is add,
the result is the sum of the elements in the list. If
the operation is mul, the result is the product of all
the elements in the list. A key issue in this design
is that the value to return in the base case depends
on the operation being applied: in short, the base
case must return the "identity element" for the given
operator, such a 0 for add and 1 for mult.
-/

def mreduce_add : list ℕ → nat
| [] := 0
| (cons h t) := h + (mreduce_add t)


#eval mreduce_add [1,2,3,4,5,6,7,8,9,10]


def mreduce_mult : list ℕ → nat
| [] := 1
| (cons h t ) := h * (mreduce_mult t)

#eval mreduce_mult [1,2,3,4,5,6,7,8,9,10]

/-
Once again we can generalize from these
examples by replacing specific details
that vary from version to version with
parameters. 

The general "reduce" function thus takes both a 
binary operation (such as add or mul) and the 
identity value for that operator as parameters. 
-/

def mreduce : (ℕ → ℕ → ℕ) → ℕ → (list ℕ) → nat
| f id [] := id
| f id (cons h t) := f h (mreduce f id t)

#eval mreduce nat.add 0 [10,9,8,7,6,5]
#eval mreduce nat.mul 1 [10,9,8,7,6,5]


/-
Filter
-/

def mfilter : (ℕ → bool) → list ℕ → list ℕ 
| p [] := []
| p (cons h t) :=
    if (p h) 
    then cons h (mfilter p t) 
    else (mfilter p t)


def lt_5 (n : ℕ) : bool :=
    n < 5


def even (n : ℕ) : bool :=
    n % 2 = 0


#eval mfilter lt_5 (countdown 10)
#eval mfilter even (countdown 10)











-- double every element of a list
def mdouble : list nat → list nat
| [] := []
| (cons h t) := cons (2*h) (mdouble t)

#eval mdouble l4

-- apply a fun to every list element
def mmap : 
    (nat → nat) → list nat → list nat
| f nil := nil
| f (cons h t) := cons (f h) (mmap f t)

#eval mmap nat.succ l4 -- Lean nat.succ

#eval mmap (λ n: nat, n*n) l4 --square



-- A function that computes the sum of
-- all the numbers in a list of nats.
def mlist_sum : list nat → nat
| nil := 0
| (cons h t) := h + mlist_sum t

#eval mlist_sum []
#eval mlist_sum l4


-- A function that computes the product
-- of the numbers in a list of nats.

def mlist_prod : list nat → nat
| nil := 1
| (cons h t) := h * mlist_prod t

#eval mlist_prod []
#eval mlist_prod l4

-- Can we generalize?

/-
Yes. Fold. Take identity element,
binary function, and list of nat,
as arguments, and "reduce" the list
using the given operator along with
its correct identity value.
-/
def mlist_fold : -- also called "reduce"
    nat → (ℕ → ℕ → ℕ) → list nat → nat
| id f nil := id
| id f (cons h t) := 
    f h (mlist_fold id f t)

#eval mlist_fold 0 nat.add l4
#eval mlist_fold 1 nat.mul l4 



-- recursion problems
-- 1. args in wrong order (in add)
-- 2. *must* use by-cases style

end mlist