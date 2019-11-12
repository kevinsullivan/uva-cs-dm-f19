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

