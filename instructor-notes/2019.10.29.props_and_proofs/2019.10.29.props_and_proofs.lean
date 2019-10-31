/-
Key differences: Predicate vs propositional logic.

(1) In propositional logic, variables range over
Boolean truth values. A variable is either Boolean
true or Boolean false. In predicate logic, variables
can range over values of many types. A variable can
represent a Boolean truth value, but also a natural
number, a string, a person, a chemical, or whatever.
Predicate logic thus has far greater expressiveness
than propositional logic.

(2) Predicate logic has quantifiers: forall (∀) and
exists (∃). These allow one to express the ideas 
that some proposition is true of, every, or of at
least one, object of some kind.

(3) Predicate logic has predicates, which you can
think of as propositions with parameters, such that
the application of a predicate to argument values 
of its parameter types gives rise to a specific
proposition about those specific argument values.
In general, some of these propositions will be true
and some won't be.

Here's an example of a proposition, in predicate
logic, that illustrates all three points. It 
asserts, in precise mathematical terms, that
every natural number is equal to itself. Even
in this simple example, we see that predicate
logic includes (1) quantifiers, (2) variables
that can range over domains other than bool,
and (3) predicates. Here eq is a 2-argument
predicate that, when applied to two values,
yields the proposition that the first one
equals the second. THe more common notation
for eq a b is a = b. 
-/
def every_nat_eq_itself := ∀ (n : ℕ), eq n n

-- (_ = _) is an infix notation for (eq _ _)
def every_nat_eq_itself' := ∀ (n : ℕ), n = n

/-
This example illustrates all three points. First,
the logical variable, n, ranges over all values of
type nat. Second, the proposition has a universal
quantifier. Third, in the context of the "binding"
of n to some arbitrary but specific natural number
by the ∀, the overall proposition then asserts that
the proposition n = n is true, using a two-argument
predicate, eq, applied to n and n as arguments, to
state this proposition.
-/

/-
It will be important for you to learn both how
to translate predicate logical expressions into
natural language (here, English), and to express
concepts stated in English in predicate logic.

Let's start with some expressions in predicate
logic. We imagine a world in which there are
people and a relation between people that we
will called "likes _ _", where the proposition
"likes p q" asserts that person p likes person
q.

What, then, do the following proposition mean,
translating from predicate logic to English?

∀ (p : Person), ∃ (q : Person), likes p q

∀ (p : Person), ∃ (q : Person), ¬ likes p q

∃ (p : Person), ∀ (q : Person), likes p q

∃ (p : Person), ∀ (q : Person), likes q p

∃ (p : Person), ∀ (q : Person), ¬ likes q p

(∀ (p : Person), ∃ (q : Person), ¬ likes p q) → 
(∃ (p : Person), ∀ (q : Person), ¬ likes q p)

(∃ (p : Person), ∀ (q : Person), ¬ likes q p) → 
(∀ (p : Person), ∃ (q : Person), ¬ likes p q)
-/

/-
One of the last two propositions is valid. 
Which one? 

In predicate logic, we can no longer evaluate
the validity of a proposition using truth
tables. What we need will instead is a proof. 

A proof is an object that we will accept as
compelling evidence for the truth of a given
proposition.

It will also be important for you to learn how
to express proofs in both natural language and
formally, in terms of the "inference rules" of
what we call "natural deduction." 

Let's go for a natural language proof of this:

(∃ (p : Person), ∀ (q : Person), ¬ likes q p) → 
(∀ (p : Person), ∃ (q : Person), ¬ likes p q)

What is says in plain English is that if there 
is a person no one likes, then everyone dislikes
somebody.

To prove such an implication we will assume
that  there is a proof of the premise (and
that the premise is therefore true), and we
will then show that given this assumption we
can construct a proof of the conclusion.

Step 1: To prove the proposition, we assume
(∃ (p : Person), ∀ (q : Person), ¬ likes q p).
Given (in the context of) this assumption, it
remains to be proved that (∀ (p : Person), 
∃ (q : Person), ¬ likes p q).

Step 2: We've assumed that there is someone
no one likes. We give that someone (whoever it
is) a name: let's say, w. What we know about 
w is that ∀ (q : Person), ¬ likes q w. That
is, we know everyone dislikes w in particular.

Step 3: To prove our remaining goal, that
(∀ (p : Person), ∃ (q : Person), ¬ likes p q), 
for each person p, we select w as a "witness"
for q: a person that we expect will make the
remaining proposition true. All that remains
to be proved now is that ¬ likes p w.

Step 4: To prove this, we just apply the fact
from step 2 that ∀ (q : Person), ¬ likes q w,
i.e., that *everyone* dislikes w, to conclude
that p, in particular, dislikes w. 

We've thus shown that if there is someone
everyone dislikes then everyone dislikes 
someone. For every (∀) person, p, it is
enough to point to w to show there is (∃) 
someone that p dislikes. While p might
dislike other people, we can be sure that
he or she dislikes w because w is someone
whom everyone dislikes. 

QED. [Latin for Quod Est Demonstratum. Thus
it is shown/proved/demonstrated.]
-/

