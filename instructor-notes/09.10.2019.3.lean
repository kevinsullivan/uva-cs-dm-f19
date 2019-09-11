#check 1
#eval 1

#eval "Hello, CS2102!"
#check "Hello, CS2102!"

#eval tt
#eval ff

#check tt

def n := 1
-- def n := 2  -- no mutable state

#eval n

def b := tt
#check b
#eval b


def n1 : ℕ := 1
def b1 : bool := (tt : bool)

def s1 : string := "Hello, World!"

def b2 : bool := "Hi!"
def s2 : string := tt
def n3 : ℕ := tt

#check λ (b : bool), tt
#reduce λ (b : bool), tt

#check λ (b : bool), ff
#check λ (b : bool), b

#check (λ (b : bool), ff) (tt)
#check (λ (b : bool), ff) (ff)

#eval (λ (b : bool), ff) (ff)
#eval (λ (b : bool), ff) (tt)

def f : bool → bool := 
    λ (b : bool), ff

#eval f tt
#eval f ff 


def neg : bool → bool :=
    λ (b : bool),
        match b with
        | ff := tt
        | tt := ff
        end

-- alternative syntax
-- Haskell-like
-- preferred
def neg' : bool → bool
| ff := tt
| tt := ff

/-
Look: the tables look like the truth tables.
We can define finite functions precisely with tables.
-/

/-
More generally we can define
functions by cases. Here's 
the Fibonacci function.
-/ 

def fib: nat → nat 
| 0 := 0
| 1 := 1
| (n' + 2) := fib n' + fib (n'+1)

#eval neg tt
#eval neg ff 

#eval neg' tt
#eval neg' ff

#eval fib 10
#eval fib 35    -- slow!


/-
Next up: Binary Boolean functions.
-/