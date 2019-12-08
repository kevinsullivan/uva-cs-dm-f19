/-
(1) Boo! Happy Halloween!
(2) You gotta love the ℕs!
(3) Notes from Tue in IN
(4) Weather warning.
(3) No exam on Tuesday. 
-/

/-
Review: We define day to be a type.
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

open day 

def d : day :=
    tue

/-
NEW IDEA: another syntax for defintions
Definition now given by a "PROOF SCRIPT"
-/

def d' : day := 
begin
    exact sat,
end



/-
***************************************
Propositions as Types, Proofs as Values
***************************************
-/


/-
We define emily's_from_cville to be a new
kind of type: a logical type as opposed to
a computational type. We understand this
*type* to represent a proposition. Now the
question, is what does it mean to have a
proof of such a proposition? 

Informally, we might say that we'll take
a driver's license, passport, or utility
bill as a proof. We can formalize this idea
by defining drivers_license, passport, and
proof to be *values* of this type! We have
a proof of a proposition if we can produce
a value of its type!
-/
inductive emily's_from_cville : Prop
/- 
Constructors define the values, which we 
now accept as "proofs" of the proposition
Proofs in Lean are values of *logical* types.
-/
| drivers_license 
| passport
| utility_bill

open emily's_from_cville 


-- Proofs represented formally as *values*
def a_proof : emily's_from_cville  := 
    passport

theorem a_proof' : emily's_from_cville :=
    utility_bill

theorem a_proof'' : emily's_from_cville  :=
begin
    exact utility_bill,
end

/-
Note the use of def in the first example and
theorem in the second. There is no practical
difference. We use "theorem" to inform the
reader that we intend to produce a proof of
a proposition.
-/


/-
****************************************
Predicates as parameterized propositions
****************************************
-/

/-
Here's aother data (computational) type.
-/
inductive person : Type
| mari
| jose
| jane
| bill

open person

inductive mari_is_from_cville : Prop
| yes_she_is

#check mari_is_from_cville 

open mari_is_from_cville

theorem mari_proof : mari_is_from_cville := yes_she_is

/-
We can generalize from a specific proposition,
such as *emily* is from charlottesville to one
that allows us to assert that any given person
is from charlottesville. We do this by adding 
a parameter.

The result is what we call a predicate. We can
say that a predicate is a proposition with a 
parameter. When applied to an argument of the 
right type, the result is again a proposition. 

Ex: inductive is_from_cville : person → Prop

The constructors of the parameterized type define 
the set of proofs that can be produced for  each
of the corresponding propositions.
-/

inductive is_from_cville : person → Prop
| proof_for : 
    ∀ (p : person), 
        p = mari → is_from_cville p

#check is_from_cville
#check is_from_cville mari
#check is_from_cville jose
#check is_from_cville jane
#check is_from_cville bill

open is_from_cville 

#check proof_for
/-
Think of a proof of a "∀" proposition 
as being like a function. A constructor
is a proof. In particular, proof_for can
be understood as a proof of the ∀ claim.
So we can treat proof_for as a function
that takes a person as an argument and
that returns a proposition, obtained by
applying the predicate on the right of 
the comma to the given argument.
-/  
#check proof_for mari
#check proof_for jose
#check proof_for bill

theorem mifc : is_from_cville mari := 
begin
    apply proof_for _ _,
    apply eq.refl mari,
end

theorem bifc : is_from_cville bill := 
begin
    apply proof_for,
    _
end

/-
What we're seeing here is what we call
the elimination principle for proofs of
∀ propositions. We can treat such a proof
as a function and apply it to a particular
object of the quantified type to get a
proof for the stated proposition *about
that particular object*.

Here' we get back proofs of proposition
such as mari = mari → is_from_cvill mari
and bill = mari → is_from_cville bill. 

Each of these is a proof of an implication,
of the form P → Q, which we can also treat
as a kind of function: if we can produce a
proof of a premise, then we can apply the
proof-of-implication/function to it to get
a proof of the conclusion. 

In this case, we will be able to construct
and thereby obtain a proof of mari = mari,
but there is no proof of bill = mari, so we
will be able to construct a proof of the
proposition, (is_from_cville mari) but not
one of (is_from_cville bill).
-/

/-
Understand that the constructors of a type are to
be understood as the "axioms," or fundamental rules
of reasoning, for a given type. They tell us exactly
how we can produce values (or proofs) of a given type
(or proposition, understood as a type).
-/

/-
As an example, suppose we to prove the proposition
that mari is from cville. Formally we'd state this
as the proposition (is_from_cville mari). To prove it, 
we need to construct a proof. To do that, we have to
use the only available "reasoning rule", which is
given by the one constructor for this type, namely:

proof_for : ∀ (p : person), p = mari → is_from_cville p

What this says is that for any person, p, *if* you
have a proof that (p = mari) then you can derive a
proof of (is_from_cville mari).

In plain English, the proof would thus go like this:

"To produce a proof of (is_from_cville mari) we first
apply the `proof_for' rule to mari to conclude that
(mari = mari) → is_from_cville mari. To prove the
conclusion, it will suffice to produce a proof of
(mari = mari). But this follows from the reflexivity
of the equality relation. QED."

Now look at what happens if we try to prove jane is 
from cville. We apply proof_for to jane, yielding the 
proposition, (jane = mari) → is_from_cville jane. The
conclusion is what we want, but to reach it, we have
to produce a proof of (jane = mari), and there is no
way to do that because jane and mari are different
people. So we are stuck, with no way to build the 
proof we require.
-/

/-
******************************************
Predicates define properties and relations
****************************************** 
-/

/-
The is_from_cville predicate defines the
"property" of being from Charlottesville.
Only mari has this property according to
our definitions, because only for mari is
there a proof.

A predicate of one argument defines proofs
for none, some, or all values of its argument
type and thereby identifies those with the
given property.

A predicate of two arguments similarly 
defines a *relation*: a set of pairs of
values that have a given property. The
equality relation is a very good example.

We accept as an axiom that there is a 
proof for every proposition of the form,
a = a, no matter what type of thing a is,
and that there are no other proofs of
equalities. (Slight footnote here.)

This idea is formalized in Lean with a
predicate called that takes two arguments 
(of any given type -- it's polymorphic),
for which there's a proof only if both
are the same. Convention infix notation
uses the = operator.
-/

#check eq 4 4
#check eq 4 5
#check 4 = 5
#check eq "Hi" "Hi"

/-
Each of these terms is a proposition/type.
There are proofs for those that are true!
The proofs are constructed by a constructor
called refl defined for the eq type. We
refer to it as eq.refl. It takes *one*
argument, a, and yields a proof/value of
type a = a. It's thus impossible to create
a proof of a = b unless a and b are really
equal to each other!
-/

#check (eq.refl 3)
#check (eq.refl "Hi")
#check (eq.refl mari)

/-
The term, (proof_for mari (eq.refl mari)), is accepted
as a value of type (is_from_cville mari), i.e., as a 
proof that mari is from charlottesville. Can we construct
a proof
-/

theorem mari_is_from_cville' : is_from_cville mari :=
begin
    apply proof_for mari _,
    exact (eq.refl mari),
    _
end

-- YAY!

theorem mari_is_from_cville'' : is_from_cville mari :=
begin
    apply proof_for _ _,    -- lean infer first arg!
    --exact mari,
    exact (eq.refl mari),
end

theorem bill_is_from_cville : is_from_cville bill :=
begin
    apply proof_for _ _,    -- lean infer first arg!
    --exact mari,
    exact (eq.refl mari),   -- no way
end

/-
End of lecture
-/


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
    zmk 0 (eq.refl 0)

/-
Even: inductively defined proofs
-/

inductive is_even : ℕ → Prop
| pf_zero_is_even : (is_even 0)
| pf_even_plus_two_is_even : 
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
    pf_even_plus_two_is_even 0 zero_is_even

theorem four_is_even : is_even 4 :=
    pf_even_plus_two_is_even 2 two_is_even

theorem ten_is_even : is_even 1000 :=
begin
    repeat { apply pf_even_plus_two_is_even },
    exact pf_zero_is_even,
end

#print ten_is_even


theorem two_is_even' : is_even 2 :=
begin
    apply pf_even_plus_two_is_even 0 zero_is_even,
end

theorem two_is_even'' : is_even 2 :=
begin
    apply pf_even_plus_two_is_even 0 _,
    exact zero_is_even,
end


theorem two_is_even''' : is_even 2 :=
begin
    apply pf_even_plus_two_is_even _ _,
    exact zero_is_even,
end

theorem two_is_even'''' : is_even 2 :=
begin
    apply pf_even_plus_two_is_even,
    exact zero_is_even,
end



theorem four_is_even' : is_even 4 :=
    pf_even_plus_two_is_even 2 two_is_even

theorem four_is_even'' : is_even 4 :=
begin
    apply pf_even_plus_two_is_even 2 two_is_even, 
end 

theorem four_is_even''' : is_even 4 :=
begin
    apply pf_even_plus_two_is_even, 
    apply two_is_even,
end 

theorem four_is_even'''' : is_even 4 :=
begin
    apply pf_even_plus_two_is_even, 
    apply pf_even_plus_two_is_even, 
    apply zero_is_even,    
end 

theorem ten_is_even' : is_even 10 :=
begin
    apply pf_even_plus_two_is_even, 
    apply pf_even_plus_two_is_even, 
    apply pf_even_plus_two_is_even, 
    apply pf_even_plus_two_is_even, 
    apply pf_even_plus_two_is_even, 
    exact zero_is_even,    
end 

#print ten_is_even'

-- Here's some automation in Lean
theorem ten_is_even'' : is_even 10 :=
begin
    repeat {apply pf_even_plus_two_is_even},
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