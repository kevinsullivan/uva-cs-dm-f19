-- propositions
-- proofs
-- predicates
    -- sets
    -- relations
    -- equality
-- connectives
    -- not
    -- and
    -- or


-- proposition
inductive nifty_was_a_cat : Prop
-- proofs
| there_are_pictures_of_nifty
| we_remember_nifty_fondly
open nifty_was_a_cat 

theorem nwac : nifty_was_a_cat := there_are_pictures_of_nifty
theorem there_is_a_natural_number : ℕ := 1

/-
-/

inductive pet : Type
| nifty -- a cat
| fido -- a dog
| cheese -- a rat
| tom -- a cat

open pet

-- predicate
inductive was_a_cat : pet → Prop
| nifty_proof : was_a_cat nifty
| tom_proof : was_a_cat tom

open was_a_cat

#check was_a_cat
#check (was_a_cat nifty)
#check (was_a_cat fido)
#check (was_a_cat cheese)
#check (was_a_cat tom)

theorem nwac' : was_a_cat nifty := 
    nifty_proof

#check nifty_proof
#check tom_proof

theorem cwac : was_a_cat cheese := _

/-
Property of a pet: that of having 
been a cat. Some have it. Some don't
-/

/-
Set of pets: { nifty, tom }.
-/

/-
How might we assert that "nifty was
a cat AND cheese was a cat"? Each of
these claims is a proposition, in turn
an object of type Prop, and what we want
to build is a bigger proposition. Rather
than a one-off solution specific to the
given propositions, we'll create a way
to conjoin any two propositions into a
larger one, a conjunction. To build
one it is necessary and sufficient 
to have proofs of each component
proposition.

We want a way to to build an AND
proposition based on any two smaller
component propositions. The type of
our proposition is Prop, and of the
smaller propositions, also Prop. So
we really need somthing of type
Prop → Prop → Prop. This is just a
Prop parameterized by two Props, 
which we might call α and β. We
need a polymorphic type. 

nifty YES
fido NO
cheese NO
tom YES
-/

#print and

namespace our_logic

/-
INTRODUCTION
Suppose α and β are propositions.
Given proofs, (a : α) and (b : β), we 
can build a proof, (and.intro a b), of 
α ∧ β.

Here are three ways to write exactly
the same inductive definition.
-/

inductive and'' (α β : Prop) : Prop
| intro : α → β → and''

-- Here we build a big prop out of two small ones
def nwac_and_cwac : Prop := 
    and'' (was_a_cat nifty) (was_a_cat cheese)

-- Here we try to construct a proof of the big prop
def pf : nwac_and_cwac := 
    and''.intro nifty_proof _

-- Here we succeed in constructing a proof of it
def pf2 : 
    and'' (was_a_cat nifty) (was_a_cat tom) :=
        and''.intro nifty_proof tom_proof

-- The proposition is a (logical) type (of type Prop)
#check and'' (was_a_cat nifty) (was_a_cat tom)
-- The proof of it is a *value* of its logical type
#check  and''.intro nifty_proof tom_proof
-- Be sure you see exactly what's going on here!
-- It's analogous to the following
#check nat -- nat is a computational (of type, Type)
#check 5 -- 5 is a value of type nat
-- The proposition is analogous to ℕ: it's a type
-- The proof is analogous to 5: a value of this type


/- 
We formalize the and left elimination rule
(P ∧ Q) → P, as a function that takes a proof
of (P ∧ Q) and that returns a proof of P. The
key ideas are that a proof of (P ∧ Q) is of
the form (and.intro p q), where (p : P) is a
proof of P and (q : Q) is a proof of Q. We
use destructuring/pattern-matching to "get
our hands on" the component proof, p, that
is one part of a larger proof of P ∧ Q. 
-/
def and''_elim_left { α β : Prop} : (and'' α β) →  α 
| (and''.intro a _) := a

#reduce and''_elim_left pf2

/-
We put two tick marks on the name and''_elim_left
because we're going to present exactly the same
function using some slightly varying approaches
to syntax. The last of our three versions is the
one we'd prefer to see. And please be aware that
Lean already provides the left and right elim
functions through its libraries. They are called
and.elim_left and and.elim_right. What you are
seeing here is exactly how these functions work.
-/

-- The corresponding right elim rule, (P ∧ Q → P)
def and''_elim_right { α β : Prop} : (and'' α β) →  β 
| (and''.intro _ b) := b

#reduce and''_elim_right pf2


/-
We define a polymorphic "and proposition builder"
with explicitly named arguments. 
-/

inductive and' (α β : Prop) : Prop
| intro (left : α) (right : β) : and'

/-
And now, for the first time, you see the use
of "structure" in Lean to (1) define a type with
one constructor, again called intro here, and with
two arguments, with names left and right, of types
a and b. The benefit of using "structure" is that
given a value, p, of this type, the names of the
fields (left and right) can be used to obtain the
field values without having to write explicit
"projection functions", such as elim_left and
elim_right.
-/
structure and (a b : Prop) : Prop :=
intro :: (left : a) (right : b)


open and 

lemma cats : and (was_a_cat nifty) (was_a_cat tom) :=
    and.intro nifty_proof tom_proof

#reduce cats.left
#reduce cats.right


/-
The Lean libraries define ∧ as an infix notation
for (and _ _). We illustrate how this is done by
"overloading" the similar looking ^ (caret) operator.
We don't try to overload ∧ here because it leads to
an ambiguous interpretation of ∧, as ∧ is already
defined by Lean. 
-/
notation P ^ Q := and P Q   -- we don't overload ∧

theorem were_cats_nifty_and_cheese :
    was_a_cat nifty ^ was_a_cat cheese :=
begin
    apply and.intro _ _,
    exact nifty_proof,
    sorry -- Stuck: no theorem obtained.
end

theorem were_cats_nifty_and_tom :
    was_a_cat nifty ^ was_a_cat tom :=
begin
    apply and.intro,
    exact nifty_proof,
    exact tom_proof,    -- Yay, it's a theorem!
end

/-
For our nicely written "and" type (without ticks)
we rewrite the elimination rules. If we have a 
proof of P ^ Q, we can obtain individual proofs
of P and Q, respectively. We define them in the
"and" namespace. This is basically just as it is 
the Lean libraries.
-/

def and.elim_left {α β : Prop} : and α β → α
| (and.intro a b) := a

def and.elim_right {α β : Prop} : and α β → β
| (and.intro a b) := b

end our_logic

/-
Now we're using Lean's libraries!
-/

-- PROPOSITIONS!!!
#check and
def P1 : Prop := 0 = 0
def P2 : Prop := 1 = 1
def P12' : Prop := eq 1 1
#check and P1 P2

-- PROOFS!!!
#check 0 = 0
#check eq 0 0

def p1 : P1 := eq.refl 0
def p2 : P2 := eq.refl 1

example : 1 = 1 + 0 := eq.refl 1

/-
Prove 0 = 0. 

Proof: Equality is reflexive. This means that
for any value, a, of any type α, a = a.

∀ {T : Type}, ∀ (t : T), t = t.

We apply this axiom to (ℕ and) 0, in 
particular, to obtain a proof that 0 = 0.
-/

def P1_and_P2' : Prop := and P1 P2
def P1_and_P2 : Prop := P1 ∧ P2     -- infix notation for and

def p1_and_p2' : P1_and_P2 := and.intro 
    p1 
    p2

def p1_and_p2 : P1_and_P2 :=
begin
    unfold P1_and_P2,
    exact and.intro p1 p2,
end

#reduce p1_and_p2
#reduce p1_and_p2'

#check @and.elim_left

#check and.elim_left p1_and_p2
#check p1_and_p2.left

#check and.elim_right p1_and_p2
#check p1_and_p2.right

#check @and.elim_left

theorem my_elim_left : ∀ (P1 P2 : Prop), P1 ∧ P2 → P1 :=
λ P1 P2 h, 
    match h with
    | and.intro a b := a
    end

/-
English language.

We are to prove P1 ∧ P2. The and introduction rule of
natural deduction tells us that it will suffice to
apply this rule to a proof of P1 and a proof of P2.
So what remains to be proved are P1 and P2. To prove
P1, that 0 = 0, the reflexive property of equality
tells us that *every* object is equal to itself. By
applying this rule to the particular value, 0, we 
obtain a proof that 0 = 0. Now all that remains to be
proved is 1 = 1. This is easily proved in the same way.
We apply the and introduction rule to the proofs of
these two lemmas, and thereby obtain a proof that 
0 = 0 ∧ 1 = 1. 
-/

#check and.intro
#check @and.intro

/-
Universal generalizations (∀ propositions)
-/

theorem th_and : ∀ {a b : Prop}, a → b → a ∧ b :=
λ a b, 
    λ pf_a pf_b,
        and.intro pf_a pf_b

#check th_and p1 p2     -- P1 and P2 are implicit args

/-
In English!
-/

/-
IMPLICATION -- 2019.11.07.Lean
-/

/-
If we have a proof that nifty was a cat ∧
cheese was a cat, then we can deduce a proof
that cheese was a cat. Such a proof must be a
part of the assumed proof of the conjunction.
-/
theorem conj_impl_left : 
    was_a_cat nifty ∧  
    was_a_cat cheese → 
    was_a_cat cheese
| pf_n_and_c := and.elim_right pf_n_and_c

/-
There what we just did is kind of amazing.
We formalized a proof of a proposition, 
"if nifty was a cat and cheese was a cat,
then cheese was a cat, as a function. That
there is such a function proves the truth
of the logical implication (proposition).
-/

/-
Note: We have not proved that cheese was a 
cat. If fact cheese wasn't a cat; he was a
rat. All we have shown is that *if* we can
come up with a proof of the conjunction then
we can "extract" its right component proof.
It does not show that we could actually ever
build a proof of the conjunction in the 
first place.
-/


/-
We see again that a proof of a conjunction
in our logic is really just a pair of proofs,
with fst and snd (left and right) projection
functions. The and.intro constructor takes a
pair of proofs and packages them up into pair
that is accepted as a proof of a conjunction.
-/

/-
Lean provides exactly such this polymorphic
logical and connective. It's called "and" has
∧ as a conventional infix notation. Here's an
example. We also take this moment to introduce
the "example" construct in Lean. It's just 
like def or theorem, in that it calls for a
value of a particular type. The difference is
that it doesn't bind the value to a name. It
is a way to prove something without storing
the proof as a named object.
-/

example : was_a_cat tom ∧ 0 = 0 := 
    and.intro tom_proof (eq.refl 0)


example : was_a_cat tom ∧ 0 = 0 := 
begin
    apply and.intro tom_proof (eq.refl 0),
end

example : was_a_cat tom ∧ 0 = 0 := 
begin
    apply and.intro tom_proof, -- arg as subgoal
    exact (eq.refl 0)
end

example : was_a_cat tom ∧ 0 = 0 := 
begin
    apply and.intro,    -- two args as subgoals
    exact tom_proof,
    exact (eq.refl 0)
end

/-
Let's write some English language proofs.
-/

/-
IMPLIES
-/

/-
What we've seen now is that a proof that an 
implication is true is a proof that *if* one
has a proof of its premise, then from that
one can obtain a proof of its conclusion.

Again, as an example, consider that from a 
proof of a conjunction one can obtain (you
can also say "deduce") a proof of either of
its conjuncts. If one has a proof of P ∧ Q,
for example, then by applying one of the two
"and elimination" axioms (rules of natural
deduction) to the proof of P ∧ Q, one can
obtain either a proof of P, or a proof of Q. 

To prove an implication we thus prove that
there is a way to transform any proof of 
its premise into a proof of its conclusion.

In natural language, we'd say that we first
*assume* that the premise is true, and then
we'd show that in the context in which we've
made that assumption, we can show that the
conclusion must be true.

Theorem: For all propositions, P and Q,
(P ∧ Q) → P. 

Proof. Suppose that P and Q are arbitrary
but specific propositions. What remains to
prove is that (P ∧ Q) → P. To prove this,
assume we have a proof of P ∧ Q. Applying
the natural deduction principle of and 
elimination (left) yields of proof of P.
QED. 

To formalize this idea, we prove such an
implication by showing that there is a
function that, *if* given a proof of the
premise as an argument is able to create
and return a proof of the conclusion. If
there is such a function in Lean (in which
case it is a total function, and so can
take *any* proof of the premise as an
argument), then from any proof of the
premise it is always possible to derive
a proof of the conclusion, so the truth
of the premise implies the truth of the
conclusion.
-/

def pf1 : ∀ (P Q : Prop), P ∧ Q → P :=
    λ P Q,
        λ h, 
            and.elim_left h

def pf1' : ∀ (P Q : Prop), P ∧ Q → P :=
    λ X Y,
        λ h, 
            and.elim_left h

-- Note that names bound by lambda do
-- not have to be P and Q. You can call
-- arguments whatever you want, as long
-- as their names are already in use.

/-
Let's take that bit by bit. We bind a name,
pf1, to a proof of ∀ (P Q : Prop), P ∧ Q → P. 

We use ∀ (P Q : Prop) to give names to two
*parameters* -- any two propositions, P and
Q -- so that we can use these names in the
rest of the proposition: P ∧ Q → P. 

We thus have the overall proposition: for 
*any* propositions, P and Q, if P ∧ Q (is
true, has a proof) then P (is true, has a
proof), i.e., P ∧ Q → P. In curt English: 
"If P ∧ Q then P."

The lambda expressions take argument values
that, in the rest of the function definition,
are *assumed* to be of the specified types. 
So in the "body" of the function, P and Q are
*assumed* to be propositions (types, of type
Prop), and h is *assumed* to be a proof (value)
of (type) P ∧ Q. 

What the expression, (and.elim_left h), then
shows is that, in the context of *the given 
assumptions*, one can construct and return 
a proof of *P*. From the assumption of the
premise follows the truth of the conclusion.
-/

/-
A proof of an implication in constructive
logic is a function: one that if given an
argument of the premise type returns a value
of the conclusion type. Recall: propositions
are types, proofs are values of such types.

We wrote the formal proof of ∀ (P Q : Prop), 
P ∧ Q → P, to make explicit the overall
proposition being proved, but we could just
as well have written it in C style. In fact,
we could have written it in any of the ways
available to define functions.

Here are various forms in which exactly the
same proof can be expressed. In the first C
style proof, we see even more clearly that
we can think of argument to functions as 
*assumptions* that we can then use in the
function body to construct a return result.
-/

def pf2 (P Q : Prop) (h : P ∧ Q) : P :=
    and.elim_left h -- from h deduce P

#check pf2      -- that's pretty cool

-- script, assume and name args in script
-- here X and Y refer to P, Q
-- better in general to keep names P, Q
def pf3 : ∀ (P Q : Prop), P ∧ Q → P :=
begin
    assume (X Y : Prop),    
    assume (h : X ∧ Y),
    exact and.elim_left h,
end

-- proof script, args already assumed
def pf4 (P Q : Prop) (h : P ∧ Q) : P :=
begin -- look: arguments are assumptions
    exact and.elim_left h,
end

-- using cases notation
def pf5 : ∀ (P Q : Prop), P ∧ Q → P
| P Q h := and.elim_left h

/-
False Elimination: ∀ (P : Prop), false → P.
-/

/-
It doesn't matter whether or not one can
ever produce a proof of a premise, because
all that a proof of an implications says
is that *if* you can give a proof of the
premise as an argument to a function, then
it can return a proof of the conclusion. 

A clear example involves the proof that
"false implies (the truth of) anything".
Formally: ∀ (P : Prop), false → P. Take
a moment to make sure you understand what
this proposition says!
-/

/-
The proposition (false : Prop) is one with
no proofs at all.
-/

inductive false' : Prop
-- no constructors!

/-
For example, it's true that (false → 0 = 1)
even though one can never produce a proof
of false. The truth of (false → 0 = 1) is
demonstrated by the existence of a function
that, *if* it could be given a proof of false, 
would return a proof of 0 = 1 by applying the
false elimination inference rule to the 
*assumed* proof of false to derive a proof
of 0 = 1. 
-/

theorem false_elim_example : false → 0 = 1 :=
    λ h, false.elim h

theorem false_elim_example' (h : false) : 0 = 1 :=
    false.elim h

example : false → 0 = 1 := λ h, false.elim h