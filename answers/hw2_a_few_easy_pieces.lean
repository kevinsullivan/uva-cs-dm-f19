/-
UVa CS Discrete Math (Sullivan) Homework #2
-/

/-
Note: We distribute homework assignments and
even exams as Lean files, as we do now for this
assignment. You will answer the questions in one 
of two ways: by writing an answer in a comment block 
(such as this one), or by writing mathematical logic 
(which is what "Lean code" is). For this assignment
you will write all your answers as simple comments.
-/

/-
This assignment has three questions, each with several 
parts. Be sure to read and answer all parts of all of
the questions.

Make a copy of this file in your "mywork" directory
the read and answer the questions by editing this fie.
When you are done, *save it*, then upload it to Collab. 
That is how you will submit work in this class. Be sure 
to double check your submission to be sure you uploaded
the right file.
-/

/-
QUESTION #1 (7 Parts, A - G) [35 POINTS]

ANSWERS HERE ARE RIGHT OR WRONG. 5 points each.

A. How many functions are there that take one
argument of type Boolean (one bit, if you prefer)
and that return one value, also of type Boolean?
Hint: We discussed this in class.

Answer : 4

B. How many functions are there that take two
arguments of type Boolean and that return
one value of type Boolean? Hint: we discussed
this in class, too. 

Answer: 16

C. How many functions are there that take three
bits of input and that return a one bit result?
Hint: We discussed this, too.

Answer: 256

D. Give a general formula that you believe to
be valid describing the number of functions
that take n bits, for any natural number, n,
and that return one bit. Use the ^ character
to represent exponentiation.

Answer: 2^(2^n). Can also be written 2^2^n,
because ^ is right-associative.

E. How many functions are there that take three
bits of input and that return *two* bits as a
result? Hint: think about both how many possible 
combinations of input bits there are. To define
a function, you need to specify which two-bit
return value is associated with each combination
of input values. The number of functions will be
the number of ways in which you can assign output
values for each combination of input values. Give
your answer in a form that involves 3 (inputs)
and 2 (output bits).

Answer here: (2^2)^2^3 = 4^8 = 2^16 = 65536. Any
of these answers will do.


F. How many functions are there that take 64 bits
of input and return a 64 bit result? Give your 
answer as an algebraic expression. The number is
too big to write it out explicitly.

Answer here: (2^64)^(2^64), or equivalent.

G. How many functions are there that take n bits of
input and return m bits of output, where n and m are
natural numbers? Give an algebraic expression as your
answer, involving the variables m and n.

Answer here: (2^m)^(2^n).

EXPLANATION: There are 2^m possible results for each
combination of inputs, and there are 2^n combinations
of inputs. So the result is obtained by multiplying 
(2^m) by itself (2^n) times, which explains why the
answer is what it is.
-/

/- 

EVERYONE GETS FREE CREDIT ON THIS PROBLEM. 35 points.

QUESTION #2 (Three parts, A - C)

Suppose you are asked to write a program, P(x), taking 
one argument, x, a "natural number", and that it must 
satisfy a specification, S(x), that defines a function 
in a pure functional programming language. 

A. Using simple English to express your answer, what 
proposition must be true for P to be accepted as a 
correct implementation of S. Hint: We discussed this in 
class.

Answer: ∀ x : ℕ, P x = S x

B. Why is testing alone generally inadequate to prove 
the correctness of such a program, P?

Answer: It's infeasible to test each of an infinite
number of inputs. We'll also take any answer that says
in effect that, there are too many inputs to test.

C. What kind of mathematical "thing" would be needed to 
show beyond a reasonable doubt that P satisfies S? You 
can give a one-word answer.

Answer: Proof. We would happily accept an answer that
gives a specific proof technique, namely "proof by
induction."

-/



/- 
QUESTION #3 (Four parts, A - D) [30 points; 5 points for
correct conjectures, 10 points for correct proofs. 2 points
and 5 points, respectively, for "being headed in the right
direction, but not getting it quite right."]

Consider a new data type, cool, that has three possible
values: true (T), false (F), and don't know (D). And now
consider the following conjecture:

For any natural number, n, the number of combinations 
of values of n variables of type cool is 3^n.

Give a proof of this conjecture by induction.

A. [5 pts] What is the first conjecture you must prove? 
Hint: substitute a specific value for n into the conjecture
and rewrite it with that value in place of n.

Answer: The "base case" conjecture is that for n=0,
the number of combinations of values of n variables
of type cool is 3^n = 1. 

B. Prove it [10 points]. Hint: One approach to proving
that two terms are equal is simply to reduce each term 
to its simplest form, and then show that the reduced terms
are exactly the same. In other words, just simplify
the expressions on each side of an equals to to show
that the values are identical.

Answer here: The number of combinations of zero things
is mathematically defined to be 1, so the base case 
conjecture is true. (We'll take any answer that gets
this idea basically right.)

C. [5 points] What is the second conjecture that you must
prove to complete your proof by induction?

Answer here: IF the number of combinations of values 
of m variables of type cool is 3^m THEN the number of 
combinations of values of (m+1) variables of type cool 
is 3^(m+1). NOTE: if you use n and n+1 here, that is a
good answer, but you'll find it easier to think about
induction hypotheses if you pick a different name for
your inductive conjecture.


D. Prove it [10 points]. Hint, to prove a proposition
of the form, P → Q, or P implies Q, you start by *assuming* 
that P is true (whatever proposition it happens to be), and 
then you show that in the context of this assumption,
that proposition Q must be true. In other words, you
want to prove that IF P is true THEN Q must be true,
too.

Answer here:

(Optional explanation: The inductive conjecture is an implication. To prove an implication, we assume that the
antecedent/condition is true, then we show that in the
context of this assumption, the conclusion must be true.)

Assume that the number of combinations of values of m
variables of type cool is 3^m. If we add one more variable
to make (m+1) variables, then for each of the three values
of the new variable, we have  (3^m) combinations with that
new value, making 3*(3^m) combination. But (and here is the
typical algebraic rewriting) 3*(3^m) = 3^(m+1). So, indeed,
IF the number of combinations of values of m variables of 
type cool is 3^m THEN the number of combinations of values
of (m+1) variables of type cool is 3^(m+1).

A complete proof by induction should include the following
idea. If you didn't write this time, it's ok, but in general
the following idea needs to be expressed. 

Key idea: Now because the base conjecture is true and the 
inductive conjecture is true, we can see that the original 
conjecture must be true: that is, For ANY natural number, n,
the number of combinations of values of n variables of type 
cool is 3^n.

You could also have said the following at the beginning of a
proof by induction: "To prove the original conjection, it will 
suffice to prove (1) the base case conjecture, and (2) the
inductive case." Then when you're done proving both cases,
you can just QED (quod est demonstatum, the Latin for "it is
shown".)
-/
