open list


/-
#1. You are to implement a function
that takes a "predicate" function and a
list and that returns a new list: namely
a list that contains all and only those
elements of the first list for which the
given predicate function returns true.

We start by giving you two predicate
functions. Each takes an argument, n,
of type ℕ. The first returns true if
and only if n < 5. The second returns
true if and only if n is even. 
-/


/-
Here's a "predicate" function that
takes a natural number as an argument
and returns true if the number is less
than 5 otherwise it returns false. 
-/
def lt_5 (n : ℕ) : bool :=
    n < 5

-- example cases
#eval lt_5 2
#eval lt_5 6

/-
Here's another predicate function, one
that returns true if a given nat is even,
and false otherwise. Note that we have
defined this function recursively. Zero
is even, one is not, and (2 + n') is if
and only if n' is.

You can think of a predicate function
as a function that answers the question,
does some value (here a nat) have some
property? The properties in these two
cases are (1) the property of being less
than 5, and (2) the property of being
even.
-/
def evenb : ℕ → bool
| 0 := tt
| 1 := ff
| (n' + 2) := evenb n'

#eval evenb 0
#eval evenb 3
#eval evenb 4
#eval evenb 5

/-
We call the function you are going to 
implement a "filter" function, because
it takes a list and returns a "filtered"
version of the list. Call you function
"mfilter".

If you filter an empty list you always
get an empty list as a result. If you
filter a non-empty list, l = (cons h t), 
the returned list has h at its head if
and only if the predicate function applied
to h returns true, otherwise the returned
value is just the filtered version of t.

A. [15 points] 

TA: Original had typo (actually due an
an unforeseen name conflict). Have the
students change all appearances of the
name, mfilter, to myfilter.

Your  task is to complete an incomplete
version of the definition of the myfilter
function. We use a Lean construct new to 
you: the if ... then ... else. It works
as you would expect from your work with
other programming languages. Replace the 
underscores to complete the definition.
-/

def myfilter : (ℕ → bool) → list ℕ → list ℕ 
| p [] := []
| p (cons h t) :=
    if p h 
    then (cons h (myfilter p t))
    else myfilter p t

/-
B. [10 points]

Here's the definition of a simple list.
-/

def a_list := [0,1,2,3,4,5,6,7,8,9]


/-
Replace the underscores in the first two 
eval commands below as follows. Replace 
the first one with an expression in which 
myfilter is used to compute a new list that 
contains the numbers in a_list that are 
less than 5. Replace the second one with 
an expression in which mfilter is used to 
compute a list containing even elements of 
a_list. You may use the predicate functions
we defined above.

Replace the third underscore with a similar
expression but where you use a λ expression
to specify a predicate function that takes
a nat, n, and returns tt if n is equal to
three and false otherwise. Hint: n=3 is
an expression that will return the desired 
bool.
-/

#eval myfilter lt_5 a_list
#eval myfilter evenb a_list
#eval myfilter (λ (n : ℕ), n = 3) a_list

#eval a_list


/-
#2.

Here's a function that takes a function, f,
from ℕ to ℕ, and a value, n, of type ℕ, and
that returns the value that is obtained by  
simply applying f to n. 
-/

def f_apply : (ℕ → ℕ) → ℕ → ℕ 
| f n := (f n)

-- examples of its use
#eval f_apply nat.succ 3
#eval f_apply (λ n : ℕ, n * n) 3

/-
A. [10 points]

Write a function, f_apply_2, that takes a 
function, f, from ℕ to ℕ, and a value, n, 
of type ℕ, and that returns (read this
carefully) the value obtained by applying 
f twice to n: the result of applying f to 
the result of applying f to n. For example,
if f is the function that squares its nat
argument, then (f_apply_2 f 3) returns 81,
as f applied to 3 is 9 and f applied to 9
is 81. 
-/

-- Your answer here

/-
TA: Original had typo: ff_apply instead of
f_apply_2. Have students change ff_apply to
f_apply_2.
-/

def f_apply_2 : (ℕ → ℕ) → ℕ → ℕ  
| f n := f (f n)

/-
B. [10 points]

Write a function f_apply_k that takes (1)
a function, f, of type ℕ to ℕ, (2) a value,
n, of type ℕ, and (3) a value, k of type ℕ,
and that returns the result of applying f 
to n k times. 

Note that f_apply applies f to n once and
ff_apply applies f to n twice. Your job is
to write a function that is general in the
sense that you specify by a parameter, k,
how many times to apply f.

Hint 1: Use recursion. Note: The result of
applying any function, f, to n, zero times
is just n.
-/

def f_apply_k : (ℕ → ℕ) → ℕ → ℕ → ℕ 
| f n 0 := n
| f n (nat.succ k') := f (f_apply_k f n k')

-- Answer here

/-
Use #eval to evaluate an expression in
which the squaring function, expressed
as a λ expression, is applied to 3 two 
times. You should be able to confirm that
you get the same answer given by using
the ff_apply function in the example above.
-/

-- Answer here

#eval f_apply_k (λ n, n^2) 3 2


/-
C. [Extra Credit]

Write a function f_apply_k_fun that takes (1)
a function, f, of type ℕ to ℕ, (2) a value,
k of type ℕ, and that returns a function that,
when applied to a natural number, n, returns
the result of applying f to n k times.
-/

def f_apply_k_fun : (ℕ → ℕ) → ℕ → (ℕ → ℕ) 
| f 0 := λ n, n
| f (nat.succ k') := λ n, f (f_apply_k f n k')

def sq_twice := f_apply_k_fun (λ n, n^2) 2
#eval sq_twice 3    -- yay!

/-
#3: [15 points]

Write a function, mcompose, that
takes two functions, g and f (in that
order), each of type ℕ → ℕ, and that 
returns *a function* that, when applied
to an argument, n, of type ℕ, returns
the result of applying g to the result 
of applying f to n.
-/

-- Answer here

def mcompose : (ℕ → ℕ) → (ℕ → ℕ) → (ℕ → ℕ)
| g f := λ n, g (f n)


-- test
#eval (mcompose nat.succ (λ n, n^2)) 4  -- 4^2+1 = 17

/-
#4. Higher-Order Functions

4A. [10 points] Provide an implementatation of
a function, map_pred that takes as its arguments 
(1) a predicate function of type ℕ → bool, (2) a
list of natural numbers (of type "list nat"), 
and that returns a list in which each ℕ value,
n,in the argument list is replaced by true (tt) 
if the predicate returns true for a, otherwise
false (ff).

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
| p [] := []
| p (cons h t) := cons (p h) (map_pred p t)


/-
4B. [10 points] Implement a function, reduce_or, 
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
| [] := ff
| (cons h t) := bor h (reduce_or t) 


/-
4C. [10points] Implement a function, reduce_and,
that takes as its argument a list of Boolean values 
and that reduces the list to a single Boolean value: 
tt if every value in the list is true, otherwise ff.
-/

-- Note: band implements the Boolean "and" function
#reduce band tt tt

-- Answer here

def reduce_and : list bool → bool
| [] := tt
| (cons h t) := band h (reduce_and t) 

/-
4D. [10 points] Define a function, all_zero, that 
takes a list of nat values and returns true if and 
only if they are all zero. Express your answer using 
map and reduce functions that you have previously
defined above. Again we recommend that you test your 
solution.
-/

-- Answer here (replace the _'s as needed)

def all_zero : list nat → bool
| [] := tt
| (cons h t) := band (h=0) (all_zero t) 

/-
Some tests
-/
#reduce all_zero []
#reduce all_zero [0,0,0,0]
#reduce all_zero [1,0,0,0]
#reduce all_zero [0,1,0,0]
#reduce all_zero [1,0,0,1]
