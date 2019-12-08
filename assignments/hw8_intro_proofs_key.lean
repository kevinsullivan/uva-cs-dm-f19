/-
CS 2102 F19, Homework #8, Predicate Logic & Proofs.
-/

/-
Is this stuff useful?

-- Functional programming is *hot*. Much of
Facebook's Messenger app is written in Reason,
for example, which is just a Java-script like
syntactic sugar on top of OCaml, which you
can now program in.

-- Boolean satisfiability, which is all 
about finding "models" of formulae in
propositional logic is hugely useful in
computer science. 
    * find Hamiltonian circuits in graphs
    * solve Sudoko programs automatically
    * generate test cases to "cover" all 
      statements in a program
    * annual SAT solver competitions

- Predicate logic
    * the language of mathematics
    * the language of specification

- Design and implementation of 
provably correct programming languages
and compilers

- Proofs: the language of verification
    * provable security
    * provable safety
    * provable privcy
-/

namespace hw8

/-
#1. Equality and proofs of equality. 
-/

/-
A. [10 points] Fill in the blank.

When we say that the binary equality relation, 
=, on objects of any type, α, is reflexive, we
mean that for any value, a, of type, α, _______.

ANSWER: a = a
-/

/- 
B. [10 points]
Complete the following definition in Lean
to formalize the proposition that 1 equals
1.
-/

def one_eq_one : Prop := 
    -- ANSWER
    1 = 1


/-
C. [10 points]
Give an English language proof of the
proposition that 1 = 1 by completing the
following incomplete proof.

To obtain a proof of 1 = 1 we apply the ________ 
property of the ________ relation to the specific
value, _________.

∀ a : α, (a, a) ∈ =; applying this to 1 gives us 
a proof of 1 = 1, in particular.

ANSWER: reflexive, equality, 1.

We apply the reflexive property of equality,
that ∀ (n : ℕ), n = n, to the value, 1, to
obtain a proof (value) of (type) 1 = 1. 
-/


/- 
D. [10 points]
Give a formal proof of this proposition
by completing the following definition.
-/

def proof_that_one_eq_one : one_eq_one :=
    -- ANSWER
    (eq.refl 1)


/- [10 points]
E. Complete the following test case to produce 
an example that suggests (correctly) that Lean
will accept a proof that two *different terms* are 
equal as long as they reduce to the same value. 
-/

-- ANSWER: Give a proposition and proof in Lean

def two_plus_two_eq_four : 2 + 2 = 4 := eq.refl 4

-- ANSWER Does eq.refl work as suggested? Yes


/-
#2. Predicates and Properties

A predicate is a "parameterized proposition". By
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

ANSWER: Two is even.

Give the rest of your natural language proof here,
and be sure to indicate which of the two rules you
are applying at each step in your reasoning.

ANSWER: To prove that two is even it will suffice
to prove that 0 is even, because 2 is two more than
0, so if 0 is even, then so is 2.

Now all that remains to be proven is that 0 is even.
But is is even by the first axiom, that zero is
even.

[In summary, 0 is even, so 2 is even, and because 2 
is even, 4 is even. Thus 4 is even.]

QED.

-/

/-
B. [10 points]

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

theorem zero_even : is_even 0 := 
    -- ANSWER
    pf_zero_is_even

/-
In this case, give a proof term without using
a begin/end proof script.
-/
theorem two_even    : is_even 2 := 
    -- ANSWER
    pf_even_plus_two_is_even 0 pf_zero_is_even

/-
In this case, give a proof using a begin/end
proof script.
-/
theorem eight_even  : is_even 8 := 
begin
    apply pf_even_plus_two_is_even _ _,
    /-
    Lean infers value of first argument,
    leaving the proof that that value is
    even to be constructed.
    -/
    apply pf_even_plus_two_is_even,
    apply pf_even_plus_two_is_even,
    apply pf_even_plus_two_is_even,
    exact pf_zero_is_even
end

/-
C. [10 points]

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

inductive is_odd : ℕ → Prop
| one_is_odd : is_odd 1
| two_plus_odd_is_odd : 
    ∀ (n : ℕ), is_odd n → is_odd (nat.succ(nat.succ n))

open is_odd

-- ANSWER

example : is_odd 1 := one_is_odd 

-- ANSWER

example : is_odd 7 := 
two_plus_odd_is_odd 
    5
    (
    two_plus_odd_is_odd 
        3
        (
            two_plus_odd_is_odd
            1
            one_is_odd  
        )
    )

example : is_odd 7 :=
begin
    apply two_plus_odd_is_odd,
    apply two_plus_odd_is_odd,
    apply two_plus_odd_is_odd,
    apply one_is_odd,   -- exact works here, too
end

 
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
    id_nat_relation.mk 3 3 (eq.refl 3)

/-
B. [10 points]

Explain in just a few words why it is not
possible to prove that (3,5) is in this relation.
-/

-- ANSWER: It's not possible to prove that (3,5)
-- is in the relation because it's not possible
-- to construct a proof of 3=5, and so it's not
-- possible to apply the mk constructor, and there
-- is no other way to obtain a proof that a pair
-- is in the id_nat_relation

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
unfold reflexive,
assume (a : ℕ),
--sorry               -- replace this
apply id_nat_relation.mk a a (eq.refl a)
end

example : reflexive id_nat_relation :=
    λ (a : ℕ), 
        id_nat_relation.mk a a (eq.refl a)

/-
B. [Double extra credit.]

Formally define what we mean by a relation being
symmetric and transitive, in the style of the above
definition of reflexive, and formally state and show
that our id_nat_reflexive relation is also symmetric
and transitive.
-/

def symmetric {α : Type} (r : α → α → Prop) :=
    ∀ (a b : α), r a b → r b a

def transitive {α : Type} (r : α → α → Prop) :=
    ∀ (a b c: α), r a b → r b c → r a c

example : 
    symmetric id_nat_relation ∧ 
    transitive id_nat_relation :=
and.intro 
-- symmetric
(
    λ (a b : ℕ),
    λ h,
    match h with
        -- only constructor for h is mk
        -- pattern matching destructures
        -- by cases
        (id_nat_relation.mk a b e) := 
            id_nat_relation.mk _ _ 
                (eq.symm e)
    end
)
-- transitive
(    
    λ (a b c : ℕ),
    λ h k,
   match h with
        (id_nat_relation.mk a b e) := 
            id_nat_relation.mk _ _
                (
                    match k with
                        id_nat_relation.mk a b f := 
                            (eq.trans e f)
                    end
                )
    end
)

example : 
    symmetric id_nat_relation ∧ 
    transitive id_nat_relation :=
begin
    apply and.intro _ _,

    -- symmetric
    assume (a b : ℕ),
    assume (h : id_nat_relation a b),
    cases h with a b e, -- new tactic 
    apply id_nat_relation.mk
        b a (eq.symm e),  -- property of =

    -- transitive
    assume a b c,
    assume h k,
    cases h with a b e,
    cases k with b c f,
    apply id_nat_relation.mk,
    exact eq.trans e f,
end


/-
We now show how we can use our 
understanding of the formal proof
to render a precise English proof.
-/
example : 
    symmetric id_nat_relation ∧ 
    transitive id_nat_relation :=
begin
/-
To prove the conjunction, we will apply
the rule of "and introduction" to proofs
of the individual conjuncts. All that then
remains to be proved are the individual
conjuncts.
-/
    apply and.intro _ _,

/-
We first prove symmetric id_nat_relation:
that ∀ (a b : α), r a b → r b a. To prove
this universal generalization, we assume
that a and b are arbitrary but specific
natural numbers and then we prove that 
r a b → r b a.
-/
    assume (a b : ℕ),
/-
To prove r a b → r b a, we apply the 
rule for → introduction: we assume that
we have a proof of the premise, r a b,
and we then show that we can obtain a
proof of the conclusion, r b a.
-/
    assume (h : id_nat_relation a b),

/-
What now remains to be proved is r b a.
To construct a proof of (r b a) our only
choice is to apply id_nat_relation.mk to
b, a, and to a proof that b = a. The only
missing element is a proof of b = a, which
we will build in the next step.
-/
    apply id_nat_relation.mk b a _,
/-
To prove that b = a, we observe that
inherent in h is a proof that a = b.
There is no other way that the proof
of h could have been obtained. 
-/
    cases h with a b e,
/-
Finally, we apply the principle of
the *symmetry* of = to (a = b) to
show that (b = a), and that is the
last proof we need to complete the
application of "mk".
-/
    apply eq.symm e,

/-
QED first conjunct.
-/

/-
To complete the proof we now prove that
id_nat_relation is transitive: namely,
that ∀ (a b c: α), r a b → r b c → r a c.
-/

/- [∀ introduction]

This conjecture is in the form of a
universal generalization. We thus
start by assuming that a, b, and c 
are arbitrary but specific natural
numbers. Then what will remain to be
proved is that r a b → r b c → r a c.
-/
    assume a b c,

/- [→ introduction]

To prove the remaining implication,
we assume that the premise is true
(and that we have a proof of it that
we will call h).
-/
    assume h,

/- [→ introduction again]

What remains to be proved is the
rest of the implication, so we once
again assume that we have a proof of
the premise. We'll call it k.
-/

    assume k,

/-
What remains to be proved is that
(a, c) is in the id_nat_relation.
To prove it, we will apply the 
axiom that if (a = c) then (a, c)
is provably in this relation. All
that will remain to be proved is
that a = c.
-/
    apply id_nat_relation.mk,

/-
To prove that a = c, we will 
first deduce from the existence
of h that a = b, and from the
existence of k that b = c, and
we will then apply the axiom of
the transitive of equality to
deduce that a = c. This will
complete the proof that our 
relation is transitive; and 
that in turn will complete the
proof that it is both symmetric
and transitive.
-/

/-
The only way that it can be
true that r a b is if a = b,
and we've assumed that r a b,
so we can deduce that (under
this assumption), a = b.
-/
    cases h with a b e,

/-
The only way that it can be
true that r b c is if b = c,
and we've assumed that r b c,
so we can deduce that (under
this assumption), b = c.
-/
    cases k with b c f,

/-
From these two equalities,
by the axiom of the transitivity
of equality we deduce that (under
the given assumptions) a = c.
-/
    exact eq.trans e f,

/-
And that compeletes both the
proof of transitivity and the
proof of both symmetry and of
transitivity of our relation.

QED.
-/
end

/-
An unambiguos, consistent, complete,
and formally precise natural-language
proof.

To prove the conjunction, we will apply
the rule of "and introduction" to proofs
of the individual conjuncts. All that then
remains to be proved are the individual
conjuncts.

We first prove symmetric id_nat_relation:
that ∀ (a b : α), r a b → r b a. To prove
this universal generalization, we assume
that a and b are arbitrary but specific
natural numbers and then we prove that 
r a b → r b a.

To prove r a b → r b a, we apply the 
rule for → introduction: we assume that
we have a proof of the premise, r a b,
and we then show that we can obtain a
proof of the conclusion, r b a.

What now remains to be proved is r b a.
To construct a proof of (r b a) our only
choice is to apply id_nat_relation.mk to
b, a, and to a proof that b = a. The only
missing element is a proof of b = a, which
we will build in the next step.

To prove that b = a, we observe that
inherent in h is a proof that a = b.
There is no other way that the proof
of h could have been obtained. 

Finally, we apply the principle of
the *symmetry* of = to (a = b) to
show that (b = a), and that is the
last proof we need to complete the
application of "mk".

QED first conjunct.

To complete the proof we now prove that
id_nat_relation is transitive: namely,
that ∀ (a b c: α), r a b → r b c → r a c.

This conjecture is in the form of a
universal generalization. We thus
start by assuming that a, b, and c 
are arbitrary but specific natural
numbers. Then what will remain to be
proved is that r a b → r b c → r a c.

To prove the remaining implication,
we assume that the premise is true
(and that we have a proof of it that
we will call h).

What remains to be proved is the
rest of the implication, so we once
again assume that we have a proof of
the premise. We'll call it k.

What now remains to be proved is that
(a, c) is in the id_nat_relation.
To prove it, we will apply the 
axiom that if (a = c) then (a, c)
is provably in this relation. All
that will remain to be proved is
that a = c.

To prove that a = c, we will 
first deduce from the existence
of h that a = b, and from the
existence of k that b = c, and
we will then apply the axiom of
the transitive of equality to
deduce that a = c. This will
complete the proof that our 
relation is transitive; and 
that in turn will complete the
proof that it is both symmetric
and transitive.

The only way that it can be
true that r a b is if a = b,
and we've assumed that r a b,
so we can deduce that (under
this assumption), a = b.

The only way that it can be
true that r b c is if b = c,
and we've assumed that r b c,
so we can deduce that (under
this assumption), b = c.

From these two equalities,
by the axiom of the transitivity
of equality we deduce that (under
the given assumptions) a = c.

And that compeletes both the
proof of transitivity and the
proof of both symmetry and of
transitivity of our relation.

QED.
-/

end hw8