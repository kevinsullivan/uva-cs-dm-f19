namespace hidden        -- you can ignore this

/-
1a. Define a polymorphic tree type. A tree of objects of type α 
is either empty or it is a value of type α along with two 
smaller trees of the same kind. You can call them left and right
respectively.
-/

/-
1b. 
Define a polymorphic function, is_empty, that takes a value of
type, tree α, and that returns Boolean tt if it is empty and ff 
otherwise.
-/

/-
1b. Define a polymorphic function, num_nodes, that takes a value 
of type, tree α, and that returns the number of nodes in the 
tree.
-/


/-
2. A bit has one of two values. Imagine a type, let's call it 
trit, with three values (e.g., true, false, and dont-know). How 
many binary functions are there, taking two values of tihs type 
and returning a value of the same type?
-/

/-
3. Define a function, sum_squares, that takes a natural number, 
n, as an argument, and that returns the sum of the squaress of 
all of the natural numbers from 0 to n, inclusive.
-/

/-
4a. We represent a binary relation, R, on a set of  values of 
some  type, α, as a predicate with two arguments. In Lean such a 
predicate is of type α → α → Prop. A property of such a relation 
is a predicate on a relation, and so is of type (α → α → Prop) → 
Prop.

Here is the definition of a property of binary relations called 
asymmetry. A relation is said to be asymmetric if whenever (x, y)
is in the relation, (y, x) is not. For example, the less-than 
relation on natural numbers is asymmetric.
-/  

def asymmetric {α : Type} (R : α → α → Prop) : Prop :=
    ∀ (x y : α), R x y → ¬ R y x

/-
Similarly, a relation is said to be irreflexive if for all x,
(x, x) is not in the relation. For example, an "is-unequal-to"
relation on the natural numbers would include (3, 4) because
3 is unequal to 4, but it would not include (3, 3) because
3 is not unqual to 3. Write a formal definition of irreflexive
in the style of the definition of asymmetric above. Start the
actual definition (after the :=) with ∀ (x : α).
-/

def irreflexive {α : Type} (R : α → α → Prop) : Prop :=
    ∀ (x : α), ¬ R x x

/-
4b. Prove that if a relation is asymmetric then it is 
irreflexive by completing the following proof.
-/

theorem asy_imp_irr : 
    ∀ (α : Type) (F : α → α → Prop),
        asymmetric F → irreflexive F :=
begin
unfold asymmetric irreflexive,  -- expand defs
_             
end

/-
5. Prove the following. You may use a tactic script,
as indicated here, or switch to another format for your
proof. Whatever you are most comfortable with is fine.
-/

example : 
    ∀ (P Q R : Prop), 
        (∀ (p : P), Q) → (∀ (q :Q), R) → (P ∨ Q) → R :=
begin
_
end 

/-
6. Prove that every natural number, n, has a successor. 
Formalize this statement using universal and existential
quantifiers: for every natural number n there exists a
natural number m such that m is the successor of n. Then
complete the proof. Finish what we've started for you.
-/

example : ∀ (n : ℕ), _ := _

/-
7. Consider a binary relation, squares, on the natural
numbers. A pair, (x, y), is in this relation if and only
if y=x^2. Formalize this relation in Lean as a predicate,
squares, with two natural number arguments and one proof 
constructor called intro. Then state and prove the simple
proposition that the pair, (7, 49), is in this relation.
-/

-- Answer here


/-
8. This question asks you to model a little world.
The world has people in it (a type) and there is a
binary relation, parent_of, on people. What is means
for a pair (x, y) to be in this relation is that x 
is a parent of y.
-/

axiom Person : Type
axiom ParentOf : Person → Person → Prop

/-
Define a GrandParentOf relation, such that (x, y) is
in this relation if and only if x is a grand parent of
y. What this means, of course, is that there is some z
such that x is the parent of z and z is the parent of y.
Define the GrandParentOf relation using an inductive 
type definition in the usual way. It needs only one
constructor, which must enforce the condition that
defines what it means "to be a grandparent of".
-/

/-
9. In simple English explain what it means for a binary
relation on a set to be

* reflexive:
* transitive: 
* symmetric:

Give an example of an everyday mathematical relation 
other than equality that is transitive.

Is the greater-than relation reflexive? Explain.

Is it symmetric? Explain.
-/


/-
10. Give a natural language proof, in your own words,
showing that the square root of two is irrational. You
may find the details of this proof easily by searching
online.
-/

/-
11. Prove formally that 0 ≠ 1, then translate your
formal proof, step by step, into an English language
proof, citing the reasoning principles that you use.
What fundamental proof strategy is centrally involved
in this proof?
-/

/-
12. Lean includes the law of the excluded middle in a
closed namespace called classical. The axiom goes
by the name, classical.em. You may apply it to any
proposition, P, to obtain a proof of P ∨ ¬ P. Use
the law of the excluded middle to show that proof
by contradiction is valid, as long as you accept
em as an axiom. Hint: We covered this in class.
-/

/-
13. Let's define a natural number to be cool if it's
either 2 or 5 or the sum or the product of two 
cool numbers. Formalize this definition in Lean
and then state and prove the proposition that 35
is cool.
-/

end hidden