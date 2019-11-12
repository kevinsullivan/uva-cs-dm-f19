/-
There are two key things we do with proofs.

(1) We build them
(2) We use them

In logic, the basic rules for building,
or constructing, proofs go by the name
of introduction rules. The basic rules
for using proofs are called elimination
rules.

Each *form* of proposition has its own
introduction and elimination rules. For
example, to build a proof of P ∧ Q, one
must use the introduction rule for and,
while using a proof of P ∧ Q relies on
the two elimination rules, which serve
to extract from a proof of P ∧ Q a proof
of P or a proof of Q.

In this class, we assume (P Q : Prop), 
(T : Type), (x y : T) then summarize, 
review,  and practice using the rules 
to build and use proofs of these forms:

- ∀ (p : P), Q  [Q usually a predicate]
- x = y
- P → Q
- P ∧ Q
- ∃ (x : P), Q  [Q usually a predicate]

A key to understanding how to build
proofs is that it's a top-down and
recursive process. For example, to
build a proof of ∀ (p : P), Q, we
use the introduction rule for ∀. It
tells us to assume that p is some
arbitrary but specific value of type
P, and then to prove Q for that p.
To do this, we recursively apply 
our approach to building proofs to
build a proof of Q, but now within
a context in which we can use the
assumption that p is some specific
value of type P. We now repeat the
same process: (1) ask what form is 
Q; (2) choose an introduction rule
for that form of proposition. Often
we need smaller proofs to apply the
introduction rules, and for this, we
use proofs we have already built or
assumed, using elimination rules as
necessary.
-/

/-
FORALL INTRODUCTION

Assume that you have an arbitrary but
specific value of the quantified type,
(p : P), then prove Q. 

Example: Prove "all balls are green".

Step 0: Formalize proposition.

∀ (b : Ball), Green b

Step 1: We start by assuming that 
b0 is an arbitrary but specific
ball, and now all that remains to
be proved is Green b (that this b
in particular) is Green.

Formally: Green b. Remaining goal.

Example: prove ∀ (n : ℕ), n = n.

Proof: We begin by supposing that
n0 is an arbitrary but specific
natural number. What remains to
be proved in this context is that
n0 = n0. [∀ intro]. 

To prove that n0 = n0 is trivial 
by the axiom that tells us that 
the equality relation is reflexive. 
Thus we have proved the proposition. 
[By reflexive property of equality.]
-/

theorem all_n_eq_n : ∀ (n : ℕ), n = n :=
    λ (n0 : ℕ), (eq.refl n0)

example : ℕ := 5

example : ∀ (n : ℕ), nat.pred (nat.succ n) = n :=
    λ (n0 : ℕ), 
        (eq.refl n0)

/- ∀ Elimination -/

/-
Example:

Prove that if every ball is green, then 
a specific ball, b0, is green.

(∀ (b : Ball, Green b)) → ((b0: Ball) → (Green b0))

See below. The elimination rule for forall is based
on the idea that we can *apply* a proof of a forall
to a specific value (an argument) to build proof 
for that specific value.
-/



/-
IMPLICATIONS

INTRODUCTION FOR → 

Assume that we have a proof of the premise.
Then in that context, construct a proof of
the rest, the conclusion.


Example: Prove
(∀ (b : Ball, Green b)) → ((b0: Ball) → (Green b0))

We begin by assuming that every ball is green,
then in this context, all that remains to be
proved is that if b0 is ball then b0 is Green.

To prove this, we assume that b0 is some specific
ball, and in this context all that remains to be
proved is: b0 is Green. This is proved by the use
of forall eliminatio n. We apply our *assumed*
proof of ∀ (b: Ball), Green b, TO b0, to obtain
a proof that b0 is green.

QED

-/

axioms (Ball : Type) (Green : Ball → Prop)

example : (∀ (b : Ball), Green b) → ∀ (b0: Ball), Green b0 :=
λ h, 
    λ a, 
        (h a)

/-
Assume that we have proof, h, that every ball is green.
In this context what remains to be proved is that any
particular ball is green.

So now we assume that b0 is some arbitrary but specific
ball, and in this extend context of assumptions, all 
that remains to be proved is that b0 is green. 

But we already have a proof that every ball is green
so all we need to is to apply it to b0, and that 
gives us a proof that b0 is green.

QED.

-/
