














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
empty or it is an element followed by a 
one-smaller list.
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
| (cons h t) := 1 + (mlength t)



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


def mdouble : list nat → list nat 
| [] := []
| (cons h t) := cons (h*2) (mdouble t)

#eval mdouble []
#eval mdouble l4

def mmap : (ℕ → ℕ) → list ℕ → list ℕ 
| f [] := []
| f (cons h t) := cons (f h) (mmap f t)

#eval mmap nat.succ [1,2,3,4]
#eval mmap (λ n : ℕ, n*n) [1,2,3,4]



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