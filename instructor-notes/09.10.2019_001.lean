/-
2102. Sept 10, 2019

A terms is an expression that represents 
a value of some type. Today we introduce
several kinds of terms and how each kind
of term is evaluted to compute the value  
it represents. The kinds of terms that we
see now are the following:

- literal
- identifier ("variable")
- lambda  ("function")
- application (fn applied to arguments)

Before we get to this material, though,
we talk briefly about *why* we need such 
a precise language as mathematical logic. 
-/

/-
Why logic: formal vs natural language.

Natural language is extremely powerful,
but the cost of that power includes the
distinct possibilities that expressions
will be

- ambiguous
- inconsistent
- uncheckable

We discussed some examples in class. If a
specification of software is written in
English, Mandarin, French, or whatever, 
the risk is great that it will be mis-
interpreted by the implementer, and the
resulting code will fail to satisfy its
*intended* specification.

Mathematical logic gives us a formal
language in which we can be much more
precise about what is required. It is of
course useful not only for software
engineering, but for all of mathematics
and computer science.
-/

/-
And now, let's start our exploration of
mathematical (specifically "predicate") logic with the concept of, and several
major kinds of, terms.
-/

/-
Literal terms.

Literal terms evaluate to the values that
they name. A literal expression and its 
value look the same, but you should see
one as an expression, and the other as a
value.
-/

-- terms of type ℕ 

#eval 1 -- literal 1 evaluates to value 1 
#eval 77

#check 77
#check nat  -- every term has a type
#check ℕ    -- even a a type is a term

-- terms of type bool

#check bool
#check tt
#check ff
#eval tt
#eval ff 

-- terms of type string

#eval "Hello, Lean!"
#eval "This is a lot of fun!"

/-
Identifer: a name bound to another term.
-/

def n := 1      -- bind n to term "1"

/-
Identifiers are not really "variables".
Once bound to a value, an identifier
cannot be re-bound to another value.
Rather, just think of an identifier as
a shorthand for the term it's bound to.

In the following line, Lean gives an error, as the identifier, n, is already 
bound to a value (namely 1).
-/

def n := 2   // no mutable store!

/-
Every term has a type. Lean sometimes
"infers" types, so you don't have to say
explicitly what the type of a term is.
For example, Lean infered that the type
of 1 is ℕ, and therefore that the type
of n must also be ℕ. 

Here we define a new identifer, m, and
*expliitly* state that it is of type ℕ.
An attempt to bind m to a value that is
not ℕ will then fail. Hover your mouse
cursor over the red line to see the error
message.
-/
def m : ℕ := 1
def k : ℕ := "Hello"

/-
Note that at this point, the *type* of
k is known (it's ℕ), but no value is bound
to k. Lean leaves the type as "sorry". A 
"sorry" tells Lean to assume that a value
of the right type is bound without saying
what that specific value is. 
-/
#check k
#eval k

def j : ℕ := 3

-- When an identifier term is evaluted, 
-- the result is the value it's bound to
-- Evaluating a "sorry" gives an error

#eval n
#eval m
#eval k
#eval j

/-
Functions
-/

-- Function types

#check bool → bool          -- unary
#check bool → bool → bool   -- binary
#check nat → nat            -- unary
#check ℕ → ℕ → ℕ 
#check ℕ → (ℕ → ℕ)  -- arrow rt assoc
#check (ℕ → ℕ) → ℕ 

-- Lambda abstractions are function values

-- take any bool, b; always return ff
def always_false : bool → bool :=
    λ b : bool, ff

-- take any bool, b; always return tt
def always_true : bool → bool :=
    λ b : bool, tt

-- take any bool, b; always return b
def ident_bool : bool → bool :=
    λ b : bool, b

/-
We stopped here in the AM section 001.
-/

/-
To express the negation function, 
we need a way to "decide" whether
b is tt or ff
-/

def neg_bool : bool → bool :=
λ b : bool,
    match b with
    | tt := ff
    | ff := tt
    end

/-
Function application expressions. If L is 
(bound to) a lambda abstraction of type X
to Y and if x is a value (an argument) of
type X, then (L x) is an application term
of type Y. If you evaluate (L x), you get the value computed of the function that L
represents applied to the argument, x.
-/

#eval always_false tt
#eval always_false ff

#eval always_true tt
#eval always_true ff

#eval ident_bool tt
#eval ident_bool ff

#eval neg_bool tt
#eval neg_bool ff