/-
CS 2102 F19, Homework #8, Predicate Logic & Proofs.
-/

namespace hw8

/-
#1. Equality and proofs of equality. 
-/

/-
A. [5 points] Fill in the blank.

When we say that the binary equality relation, 
=, on objects of any type, α, is reflexive, we
mean that for any value, a, of type, α, _______.

ANSWER: 
-/


/- 
B. [5 points]
Complete the following definition in Lean
to formalize the proposition that 1 equals
1.
-/

def one_eq_one : Prop := 
    -- ANSWER
    _


/-
C. [5 points]
Give an English language proof of the
proposition that 1 = 1 by completing the
following incomplete proof.

To obtain a proof of 1 = 1 we apply the ________ 
property of the ________ relation to the specific
value, _________.

ANSWER: 
-/


/- 
D. [5 points]
Give a formal proof of this proposition
by completing the following definition.
-/

def proof_that_one_eq_one : one_eq_one :=
    -- ANSWER
    _


/- [5 points]
E. Complete the following test case to produce 
an example that suggests (correctly) that Lean
will accept a proof that two *different terms* are 
equal as long as they reduce to the same value. 
-/

-- ANSWER: Give a proposition and proof in Lean

def two_plus_two_eq_four : _ := _

-- ANSWER Does eq.refl work as suggested? _____ 


/-
#2. Predicates and Properties

A predicate is a parameterized proposition. By
applying a predicate to different arguments, we get
different propositions. Such a propopsition can 
be said to be "about" the argument to which it was 
applied. 

We interpret such a proposition as asserting that 
its argument has a *property* of interest. If the
proposition has a proof (is true), the object does
have the asserted property, and if the proposition
is not true, the object doesn't have that property.

In the  following set of problems, we will take the 
property of a natural number "being even" as a case
in point. 

In natural language, we will say that a natural 
number, n, is even if and only if (1) it is zero,
or, (2) it is two more than another even number.

Think about this inductive definition. Why does it
cover all possible cases -- an infinitude of cases?
(No need for an answer here.)
-/

/-

A. [10 points]

We have accepted as *axioms* in our definition
of evennness that zero is even and that any number
that is two more than another even number is even.
These are the only axioms you may use in giving a
proof that four is even. Give a natural language 
proof now. Hint, start by saying the following:

Proof: To prove that four is even, *it will suffice*
to show that 2 is even, because if two is even then,
given that 4 is two more than two, if two is even
then so is four, by rule (2). Now all that remains
to be proved is that _______________.

Give the rest of your natural language proof here,
and be sure to indicate which of the two rules you
are applying at each step in your reasoning.

ANSWER: 

-/

/-
B. [15 points]

We formalize a predicate, such as is_even, as a
family of "inductive propositions" given by a
function from argument values to propositions. 
Such an inductive definition thus has the type, 
α → Prop, where α is the type of argument to 
which the predicate is applied. 

Please see the first line of the definition of 
is_even that follows for an example.

Having specified the *type* of a predicate, in
this case from ℕ → Prop, we then define the set
of constructors to define the logical rules that
can be used to construct proofs of any such
proposition. 

These rules are the (formal) axioms that can be
used to construct proofs. The first one (below)
states that the term, pf_zero_is_even, is to be
accepted as a proof of is_even 0 (which is how
we write the application of a predicate to a value
to obtain a proposition, here that "0 is even").

The second constructor/axiom/rule provides a way
to build a proof of (is_even 2+n) by applying the
constructor to any n along with a proof that that
particular n is even. (Yes: the ∀ specifies the
first argument to pf_even_plus_two_is_even. This
is necessary to give the argument a name, here n,
so that that name can be used in defining the rest
of the constructor's type). 
-/

inductive is_even : ℕ → Prop
| pf_zero_is_even : (is_even 0)
| pf_even_plus_two_is_even : 
    ∀ (n : ℕ), is_even n → is_even (nat.succ (nat.succ n))

/-
Give formal proofs for each of the following
propositions. (Notice how we obtain different
propositions by applying the predicate, is_even,
to different argument values. This is what we
mean when we say that a predicate defines a
family of propositions.)
-/

open is_even

theorem zero_even   : is_even 0 := 
    -- ANSWER
    _

/-
In this case, give a proof term without using
a begin/end proof script.
-/
theorem two_even    : is_even 2 := 
    -- ANSWER
    pf_even_plus_two_is_even _ _

/-
In this case, give a proof using a begin/end
proof script.
-/
theorem eight_even  : is_even 8 := 
begin
    apply pf_even_plus_two_is_even,
    sorry   -- replace this with answer
end

/-
C. [15 points]

Formally specify a predicate, is_odd, on the 
natural numbers.  You can reason about any
natural number being odd using two rules, just
as for being even. Once you've defined your
predicate (an inductive family of proposition,
just like is_even), formally state and prove
the following propositions (however you wish).

- 1 is odd
- 7 is odd

-/

-- ANSWER

open is_odd

-- ANSWER


-- ANSWER



/-
Introducing an important concept. In the preceding
problems, we've seen that we can think of a predicate
with one argument as defining a property objects, such
as the property of being even. Now we shift perspective
from the concept of a property, per se, to the concept
of "the set of objects that have a given property." The
set of objects that have the is_even property, for
example, could be written as

    evens = {0, 2, 4, 6, 8, 10, ...}

or more formally as

    evens = { n : ℕ | is_even n}

The elements of these sets are all, and only,
the values that "satisfy" the is_even predicate.
A value satisfies its predicate if, when plugged
in, the resulting proposition has a proof (and so
is true). The key conclusion is that a predicate
with a single argument defines a *set*, namely 
the set of all and only those objects that have
that property.
-/

/-
#4. Predicates and binary relations

Mathematicians define *binary relations* as sets
of ordered pairs. For example, the equality relation
on natural numbers comprises the set of of all pairs
of natural numbers such that the first and second
elements are the same. We could write this set like
this:

    equals = { (0,0), (1,1), (2,2), ...},

or like this:

    equals = { (m : ℕ, n : ℕ) | m = n }

We formalize binary relations as predicates with 
*two* arguments. The type of such a predicate in 
Lean is thus α → β → Prop, where α and β are the
types of the arguments.

In our example, we have a two-place predicate that
defines the set of ordered pairs of natural numbers
where the two elements of each pair are co-equal.

Study and understand the following specification
of this binary relation. Look at the construtor,
mk, in particular: it says that you can construct
a proof that a pair of values, n and m, is in our
id_nat_relation if you have a proof of n = m. (In 
other words, it suffices to show that n = m using
Lean's built in equality relation to construct a
proof that (n, m) is in our id_nat_relation.) 
-/

inductive id_nat_relation : ℕ → ℕ → Prop
| mk : ∀ (n m : ℕ), n = m → id_nat_relation n m

/-
A. [10 points]

Give a formal proof that id_nat_relation contains 
the pair, (3, 3). Do it by completing the following
proof. Think carefully about the third argument: you
need a *value* of what type here? What do we call a
value of a logical type?
-/

theorem three_three_in_id : id_nat_relation 3 3 :=
    -- ANSWER (apply a constructor, of course)
    id_nat_relation.mk _ _ _

/-
B. Explain in just a few words why it is not
possible to prove that (3,5) is in this relation.
-/

-- ANSWER



/-
EXTRA CREDIT.
-/

/-
Here's a definition of what it means for a
relation to be reflexive.
-/

def reflexive {α : Type} (r : α → α → Prop) :=
    ∀ (a : α), r a a

/-
A. Formally state and prove that id_nat_relation
is reflexive. Hint: use a script and start it
with "assume (a : ℕ)". Remember that to prove a ∀
proposition, we *assume* that we're given some
arbitrary but specific value of the given type,
then we prove the rest of the proposition about
it. But because we didn't say anything about 
the element we picked, we can conclude that the
statement must be true of any element of the type. 
-/

-- ANSWER

theorem id_nat_refl : reflexive id_nat_relation :=
begin
assume (a : ℕ),
sorry               -- replace this
end

/-
B. [Double extra credit.]

Formally define what we mean by a relation being
symmetric and transitive, in the style of the above
definition of reflexive, and formally state and show
that our id_nat_reflexive relation is also symmetric
and transitive.
-/


end hw8