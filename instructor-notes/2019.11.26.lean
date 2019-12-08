/-
There are direct parallels between
computational and logical types. The
unit data type corresponds to the
propositional/logical type, true: 
each has one value/proof. The empty
data type has no constructors and so
has no values. It is an uninhabited
data type. It corresponds directly 
to the proposition, false: a logical
type with no constructors and thus 
no proofs. That is just what makes
it false!
-/

#check unit
#print unit

#check empty
#print empty

#check true
#print true
#print false

/-
The true proposition is trivially provable. 
And that is what makes it always true. The
introduction rule is called true introduction
or, in Lean, true.intro.
-/
theorem trueIsTrue : true := true.intro

/-
There is no proof of false, and thus there
is no introduction rule for false!
-/
theorem falseIsTrue : false := _    -- stuck

/-
There is however an elimination rule for
false. The intuition is that if you ever
get to a place where you've deduced a proof
of false, then you must have made an invalid
assumption along the way, so it makes no 
sense to reason any further, and the current
goal, whatever it is, can simply be ignored.
Note that arguments to functions are assumed
values! The following example show that if 
you assume you are given a proof of false,
then even a crazy goal can be "discharged",
here the goal of showing 0 = 1.
-/
def falseImpliesCrazy (f : false) : 0 = 1 :=
false.elim f

/-
The preceding function definition is
equivalent to the following proof of
the smae implication. 
-/
example : false → 0 = 1 :=
λ (f : false), 
    false.elim f

/-
We can now generalize to a universal
law of predicate logic: that for any
proposition, P, false → P. This is the
rule called ex falso quod libet: from
false anything follows.
-/
example : ∀ (P : Prop), false → P :=
λ (P : Prop),
    λ (f : false),
        false.elim f 

/-
We can not introduce and understand
the concept of logical negation. If
P is an proposition, then not P, or
¬ P for shorthand, is the negation
of P. It asserts that P is false.
What that means in turn is that there
can be no proof of P. We will now see
how to prove that P is false. This
leads us to the "proof strategy" of
"proof by negation."
-/


/-
To show that P is false, show that
assuming that P is true enables one
to derive a proof of false, i.e., it
leads to a contradiction. Given that
a proof cannot be, the assumption
that there is a proof of P must
have been incorrect. Therefore 
there is no proof of P, P is false,
and we can now state correctly that
¬ P is true.
-/

#print not

/-
KEY IDEA: ¬ P is defined to mean
P → false. So whenever you see
¬ P, remember that it literally
means P → false. If you are asked
to prove ¬ P, proceed by trying 
to prove P → false. You'd do this
by assuming P and showing that that
leads to a contradiction and thus
a proof of false. Again, this is 
the strategy of proof by negation.
It's just the definition of ¬. 
-/

/-
To facilitate the following 
examples, we will now assume that
P is some arbitrary proposition.
-/
axiom P : Prop

/-
Now ¬ P is also a proposition.
-/
#check ¬ P

/-
And it is defined to mean P → false.
-/
#reduce ¬ P

/-
Proof by negation! Assume P, show
that that enables one to deduce a
proof of false.
-/
example : ¬ P :=
λ (p : P),
    _
    
/-
Contradiction. Key idea: a proof of
P → false can be *applied* to a proof
of P to derive a proof of false. From
there, as the next example shows, one
can use false elimination to complete
any proof.
-/
example : P → ¬ P → false :=
λ (p :P),
    λ (np : ¬ P),
        (np p)

example : P → ¬ P → false :=
begin
    assume (p : P),
    assume (np : P → false),
    exact (np p),
end

/-
We want to prove that if P is true
then if ¬ P is also true then 0 = 1
is true. Assume P is true and that 
¬ P is also true and show that false
is true. Apply ¬ P to P to get false.
QED.
-/

example : P → ¬ P → 0 = 1 :=
begin
assume (p : P),
assume (np : ¬ P),
exact false.elim (np p),
end

/-

    *** The or ∨ Connective ***

-/

/-
We assume now that Q is a proposition
and that we have a proof of it, q.
-/
axiom Q : Prop
axiom q : Q

/-
There are two introduction rules for or.
The first, or.inl takes a proof of P and
returns a proof of P ∨ Q. The second, inr,
takes a proof of Q and returns a proof of
P ∨ Q. The following example illustrates
the use of inr, as inl cannot be used in
this case (because we don't have a proof
of P).
-/
example : P ∨ Q :=
or.inr q

example : 0 = 1 ∨ 2 = 2 :=
or.inr 
    (eq.refl 2)

example : (P ∧ Q) ∨ Q := 
or.inr q

-- or.intro_right (0 = 1) rfl
/-
In classical but not in constructive logic,
P ∨ ¬ P is true for any proposition P. We
have to add this as an axiom to Lean if we
want to reason "classically" when using this
proof assistant.
-/


/-
Reminder: What does ¬ P mean?
-/

-- CONSTRUCTIVE LOGIC
example : P ∨ ¬ P :=
begin
_
end

-- CLASSICAL LOGIC
axiom em : ∀ (P : Prop), P ∨ ¬ P

#check em Q

example : ∀ (P : Prop), ¬ (¬ P) → P :=
begin
assume (P : Prop),
assume (nnp : ¬ ¬ P),
cases (em P),
exact h,
have f : false := (nnp h),
exact false.elim f,
end

example : ∀ (P : Prop), ¬ (¬ P) → P :=
λ (P : Prop),
    λ (nnp : ¬ ¬ P),
        match (em P) with
        | or.inl p := p
        | or.inr np := false.elim 
            (nnp np)
        end

/-
Proof by contradiction. Want to show
P. Show that ¬ P → false. That is, show
¬ ¬ P. Use theorem that ¬ ¬ P → P, which
requires the law of the excluded middle.
-/


/-
Being a proof of a universal generalization, 
we can *apply* em to any proposition, P, to 
obtain a proof of P ∨ ¬ P. 
-/
example : P ∨ ¬ P :=
em P

example : Q ∨ ¬ Q :=
em Q

#check em Q

/-
What we do to use** such a proof, or any
proof of a disjunction, P ∨ Q, is to reason
by case analysis. The goal will be to show
that (P ∨ Q) → R. The challenge is that P 
∨ Q can be true because P is or because Q
is. So to show that R follows logically 
from (P ∨ Q), we need to show that it
follows *in either case*. That is, we'd
need to show that P → R and Q → R. If both
cases are true, then R must be true no
matter why P ∨ Q is true (either because P
is or because R is).
-/

axioms 
    (R : Prop) 
    (p : P) 
    (pr: P → R) 
    (qr: Q → R)

example : (P ∨ Q) → R :=
λ (pq : P ∨ Q), 
    -- case analysis on pq!!!
    match pq with
    | or.inl pfP := pr p      
    | or.inr pfQ := qr q
    end

example : (P ∨ Q) → R :=
begin
assume pq,
cases pq with pfP pfQ,
apply pr pfP,
apply qr pfQ,
end

/-
Proof by negation. To prove ¬ P, assume P and
show that that assumption can be used to produce
a contradiction.
-/

example : ¬ false :=
λ (f : false), f

-- do this with a tactic script

example : ∀ (P : Prop), ¬ (P ∧ ¬ P) :=
λ (P : Prop),
    λ (h : P ∧ ¬ P),
        (h.right h.left)

-- do this with a tactic script

/-
Existential quantification!
-/

#print exists

example : ∃ (n : ℕ), n * n = 81 :=
    exists.intro 9 rfl

example : ∃ (n : ℕ), n * n = 81 :=
begin
    apply exists.intro _ _,
    exact 9,
    exact rfl,
end

-- let's make up another exercise

axiom Ball : Type
axiom isGreen : Ball → Prop
axiom isBlue : Ball → Prop

example : 
    (∃ (b : Ball), isGreen b ∧ isBlue b) → 
    ∃ (b : Ball), isGreen b :=
begin
assume h,
cases h with w pf,
apply exists.intro w _,
exact pf.left,
end


axiom Person : Type
axiom Likes : Person → Person → Prop

example : 
    (∃ (p : Person), ∀ (q : Person), Likes q p) → 
    (∀ (x : Person), ∃ (y : Person), Likes x y ) 
    := 
λ h, 
    λ p, 
        match h with
        | (exists.intro w pf) :=
           exists.intro w (pf p)
        end

example : 
    (∃ (p : Person), ∀ (q : Person), Likes q p) → 
    (∀ (x : Person), ∃ (y : Person), Likes x y ) 
    := 
begin
assume h,
assume p,
cases h with w pf,
exact exists.intro w (pf p)
end


def even : nat → Prop
| n := n % 2 = 0

example : exists (n : nat), even n :=
_

example : exists (n : nat), even n :=
begin
apply exists.intro 2 _,
unfold even,
exact eq.refl 0,
end


example : ∀ (n : ℕ), n = 0 ∨ n ≠ 0 :=
λ n,
    match n with
    | nat.zero := or.inl (eq.refl 0)
    | (nat.succ n') := or.inr 
    (λ h, 
    match h with 
    end)
    end 









































axiom Person : Type
axiom Likes : Person → Person → Prop

example : 
    (∃ (p : Person), ∀ (q : Person), Likes q p)  → 
    (∀ (p : Person), ∃ (q : Person), Likes p q)
    := 
begin
assume (h : (∃ (p : Person), ∀ (q : Person), Likes q p)),
assume (p : Person),
cases h with w pf,
apply exists.intro w (pf p),
end

example : 
    (∃ (p : Person), ∀ (q : Person), Likes q p)  → 
    (∀ (p : Person), ∃ (q : Person), Likes p q)
    := 
λ (h : (∃ (p : Person), ∀ (q : Person), Likes q p)), 
    λ (p : Person),
        match h with
        | exists.intro w pf := exists.intro w (pf p)
        end

-- cases is implemented by pattern matching!
-- By destructuring h and giving names to its parts.
-- I.e., h must be of the form (exists.intro w pf).
-- Giving names to the parts enables us now to
-- construct the proof of the conclusion by
-- using exists.intro applied to w, and to a
-- proof about w built by applying pf to w.


-- Short version!
example : 
    (∃ (p : Person), ∀ (q : Person), Likes q p)  → 
    (∀ (p : Person), ∃ (q : Person), Likes p q)
    := 
λ h p,
    match h with
    | exists.intro w pf := 
        exists.intro w (pf p)
    end


example : ∀ (b : bool), bor b tt = tt :=
begin
assume b,
cases b with T F,
apply eq.refl tt,
apply eq.refl tt,
end


example : ∀ (n : ℕ), n = 0 ∨ n ≠ 0 :=
begin
assume (n : ℕ),
cases n,
apply or.inl (eq.refl 0),
apply or.inr _,
assume h,
cases h,
end

example : ∀ (n : ℕ), n = 0 ∨ n ≠ 0 :=
λ n, 
match n with 
| nat.zero := or.inl (eq.refl 0) 
| (nat.succ n') := or.inr (
    λ h,
        match h with
        end
)
 end 

axiom Rel : Person → Person → Prop

example: 
    symmetric Rel → 
    ∀ (p1 p2 : Person), Rel p1 p2 → Rel p2 p1 :=
begin
assume h,
intros p1 p2,
assume r,
unfold symmetric at h,
exact (h r),
end


example :   (¬ ∃ (p : Person), ∀ (q : Person), ¬ Likes p q) → 
            (∀ (p : Person), ∃ (q : Person), Likes p q) :=
begin 
assume h,
intro p,
apply exists.intro p _,
end

∧
∨ 
¬
→ 
↔
∀
