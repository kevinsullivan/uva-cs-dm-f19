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

Here's an example of a proposition in predicate
logic that illustrates all three points. It states
in precise mathematical terms that every natural
number is equal to itself. 
-/

def every_nat_eq_itself := ∀ (n : ℕ), eq n n

/-
This example illustrates all three points. First,
the logical variable, n, ranges over all values of
type nat. Second, the proposition has a universal
quantifier, asserting a subsequent claim about all
values in the given domain of natural numbers. And,
third, in the context of the "binding" of n to some
arbitrary but specific natural number by the ∀, the
proposition then asserts that a proposition about n
it true using a two-argument predicate, eq. This is
a predicate that asserts equality of two terms, and
is usually written in infix notation as =. We can
thus write the same proposition more naturally as
follows.
-/

def every_nat_eq_itself' := ∀ (n : ℕ), n = n.

/-
It will be important for you to learn both how
to translate predicate logical expressions into
natural language (here, English), and to express
logical concepts in English in predicate logic.

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
One of the last two propositions is valid, in
the sense that it's true no matter what Person
and likes mean. Which is it? 

In predicate logic, we no longer evaluate the
validity of a proposition using truth tables.
What we need instead is a proof. A proof is a
kind of mathematical object that we accept as
compelling evidence for the truth of a given
proposition.

It will be important for you likewise to learn
to express proofs in natural language, and to
understand that, just like propositions and
predicates, they be formalized as mathematical
expressions/objects/values.

Let's go for a natural language proof of this:

(∃ (p : Person), ∀ (q : Person), ¬ likes q p) → 
(∀ (p : Person), ∃ (q : Person), ¬ likes p q)

What is says is that if there is a person that
no one likes, then everyone dislikes somebody.

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

/-
So what are the *valid* forms of reasoning
that we are allowed to use in constructing
proofs of propositions in predicate logic? 
The answer is that we already have a fairly
complete set from propositional logic that
we are now validating! Warning: a few of the
following rules are not valid. We will take
the valid ones as *axioms* for use in proofs
of propositions in predicate logic.

def true_intro : pExp := pTrue
def false_elim := pFalse ⇒ P
def and_intro := P ⇒ Q ⇒ (P ∧ Q)   
def and_elim_left := (P ∧ Q) ⇒ P   
def and_elim_right := (P ∧ Q) ⇒ Q  
def or_intro_left := P ⇒ (P ∨ Q)
def or_intro_right := Q ⇒ (P ∨ Q)
def or_elim := (P ∨ Q) ⇒ (P ⇒ R) ⇒ (Q ⇒ R) ⇒ R
def iff_intro := (P ⇒ Q) ⇒ (Q ⇒ P) ⇒ (P ↔ Q)
def iff_elim_left := (P ↔ Q) ⇒ (P ⇒ Q)
def iff_elim_right := (P ↔ Q) ⇒ (Q ⇒ P)
def arrow_elim := (P ⇒ Q) ⇒ P ⇒ Q
def affirm_consequence := (P ⇒ Q) ⇒ Q ⇒ P
def resolution := (P ∨ Q) ⇒ (¬ Q ∨ R) ⇒ (P ∨ R)
def unit_resolution := (P ∨ Q) ⇒ (¬ Q) ⇒ P
def syllogism := (P ⇒ Q) ⇒ (Q ⇒ R) ⇒ (P ⇒ R)
def modus_tollens := (P ⇒ Q) ⇒ ¬ Q ⇒ ¬ P
def neg_elim := ¬ ¬ P ⇒ P
def excluded_middle := P ∨ ¬ P
def neg_intro := (P ⇒ pFalse) ⇒ ¬ P
def affirm_disjunct := (P ∨ Q) ⇒ P ⇒ ¬ Q
def deny_antecedent := (P ⇒ Q) ⇒ (¬ P ⇒ ¬ Q)

-/


/-
Finally, we get to the main idea behind automation
of logic in tools like Lean: we represent predicate
logic propositions as special types and values of
these types as proofs of the propositions. Each of
the propositions above then describes the type of
a function that operates on such proofs, taking 
proofs and propositions as arguments and returning
them as results.
-/

/-
That sounds super-complicated but let's make it
super-easy. We'll do this by defining an ordinary
type (day) and its values, and by then defining 
a logical type -- a proposition represented as a
type -- and its values, its proofs. Here we go.
-/


/-
We define day to be a new type.
-/
inductive day : Type
/-
Type is the type of *computational* types.
Constructors define the values of the type.
-/
| mon 
| tue
| wed
| thu
| fri
| sat
| sun

/-
Now we can define variables of this type.
-/
def d : day := day.mon

/-
A proposition with proof constructors.
-/
inductive emily's_from_cville : Prop
/- 
Constructors define the proofs of the proposition
Proofs in Lean are values of *logical* types.
-/
| drivers_license 
| passport
| utility_bill

open emily's_from_cville 

def a_proof : emily's_from_cville  :=
    passport

theorem a_proof' : emily's_from_cville  :=
    drivers_license



/-
Another data (computational) type.
-/
inductive person : Type
| mari
| jose
| jane
| bill

open person

/-
A predicate is a proposition with a parameter.
When applied to an argument of the right type,
the result is a proposition. The constructors
define the set of proofs of the corresponding
propositions.
-/

inductive is_from_cville : person → Prop
| jose_birth_cert : is_from_cville jose
| jane_birth_cert : is_from_cville jane

open is_from_cville 

theorem 
jane's_from_cville : 
is_from_cville jane :=                              jane_birth_cert


/-
Some comments about function definitions.
Consider the following simple definition.
-/

def evenb (n : ℕ) : bool :=    
    n % 2 = 0

#eval evenb 3
#eval evenb 4

#check evenb

def evenb' : ℕ → bool :=
    λ n, n % 2 = 0

def evenb'' : Π (n : ℕ), bool :=
    λ n, n % 2 = 0

#eval evenb'' 5

def evenb''' : ∀ (n : ℕ), bool :=
    λ n, n % 2 = 0

#eval evenb''' 6

/-
Predicates are often used to represent properties
of objects, here, a property of people, namely
the property of a person being from Cville.
-/

inductive is_zero : ℕ → Prop
| zmk: ∀ (n : ℕ), n = 0 → is_zero n

open is_zero

theorem zero_is_zero_0 : is_zero 0 :=
    zmk 0 rfl

/-
Even: inductively defined proofs
-/

inductive is_even : ℕ → Prop
| pf_zero_is_even : (is_even 0)
| pf_n_minus_two_is_even : 
    ∀ (n : ℕ), is_even n → is_even (nat.succ (nat.succ n))

open is_even 

theorem zero_is_even : is_even 0 :=
    pf_zero_is_even

theorem zero_is_even' : is_even 0 :=
begin
    exact pf_zero_is_even
end

/-
Inductive
-/

theorem two_is_even : is_even 2 :=
    pf_n_minus_two_is_even 0 zero_is_even

theorem two_is_even' : is_even 2 :=
begin
    apply pf_n_minus_two_is_even 0 zero_is_even,
end

theorem two_is_even'' : is_even 2 :=
begin
    apply pf_n_minus_two_is_even 0 _,
    exact zero_is_even,
end


theorem two_is_even''' : is_even 2 :=
begin
    apply pf_n_minus_two_is_even _ _,
    exact zero_is_even,
end

theorem two_is_even'''' : is_even 2 :=
begin
    apply pf_n_minus_two_is_even,
    exact zero_is_even,
end



theorem four_is_even : is_even 4 :=
    pf_n_minus_two_is_even 2 two_is_even

theorem four_is_even' : is_even 4 :=
begin
    apply pf_n_minus_two_is_even 2 two_is_even, 
end 

theorem four_is_even'' : is_even 4 :=
begin
    apply pf_n_minus_two_is_even, 
    apply two_is_even,
end 

theorem four_is_even''' : is_even 4 :=
begin
    apply pf_n_minus_two_is_even, 
    apply pf_n_minus_two_is_even, 
    apply zero_is_even,    
end 

theorem ten_is_even' : is_even 10 :=
begin
    apply pf_n_minus_two_is_even, 
    apply pf_n_minus_two_is_even, 
    apply pf_n_minus_two_is_even, 
    apply pf_n_minus_two_is_even, 
    apply pf_n_minus_two_is_even, 
    exact zero_is_even,    
end 

#print ten_is_even'

theorem ten_is_even'' : is_even 10 :=
begin
    repeat {apply pf_n_minus_two_is_even}, 
    exact zero_is_even,    
end 

inductive successor_of : ℕ → ℕ → Prop
| mk : ∀ (n : ℕ), successor_of (nat.succ n) n

theorem five_succ_four : successor_of 5 4 :=
    successor_of.mk 4

inductive equal_to_nat : ℕ → ℕ → Prop
| refl : ∀ (n : ℕ), equal_to_nat n n

theorem five_equals_five : equal_to_nat 5 5 :=
    equal_to_nat.refl 5

theorem five_equals_five' : equal_to_nat 5 5 :=
begin
    apply equal_to_nat.refl _,
end

inductive equal_to_nat' (n : ℕ) :  ℕ → Prop
| refl : ∀ (n : ℕ), equal_to_nat' n 

#check equal_to_nat 
#check equal_to_nat'

theorem five_eq_five'' : equal_to_nat' 5 5 :=
    equal_to_nat'.refl 5 5

inductive equal_to {α : Type} : α → α → Prop
| refl : ∀ (a : α), equal_to a a