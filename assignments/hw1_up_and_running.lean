/-
This text isn't formal logic or code. It's natural 
language text embedded into a formal logic or code 
file, otherwise known as a "comment". This comment
explains what to for this assignment.

Each of the following lines of logic asserts that
an identifer (such as n on the first line) can be
found to a value of a specific type (such as natural
number, written in our formal logic as nat or ℕ).

Your job is to "prove" that each such assertion can
be made true by filling in a specific value of the
required type in place of the placeholders, denoted
by underscores. These formal name for placeholders 
is meta-variables.

In other words, fill in values of the right types
in place of the specified metavariables. Then save
your file and upload it as your submission for the 
Homework #1 assignment on Collab.

The purpose of this assignment is to make sure that
you've got everything working that you'll need to be 
able to get your work done in this class.

This assignment is due by 9AM on Thursday, Sept. 5.

Note, values of type ℕ include 0, 1, 2, 33, etc. 
Values of type string include "Hello, World!" and
"This is really fun!" And the two values of type
bool, in Lean, are tt (for true) and ff (for false).
-/

/-
Edit this code by replacing the placeholders with
specific values. Note the red squiggly underlines
under the underscores (placeholders). They indicate
an error condition, specifically Lean doesn't know
enough to fill in (synthesize) values. That's why
we're asking you to fill them in. 
-/

def n : nat := _

def s : string := _

def b : bool := _

/-
Have you succeeded? To know the answer, you should 
first check that the red underlines above have gone 
away. Second, both the #check and #eval commands
below should be without errors. The #check command
tells you the type of value that is expected to be
bound to an identifier. The #eval command tells you
what value is bound. If no value is bound because
you've used a placeholder instead of a value, the
#eval commands will fail (with a red squiggle) and
an error message saying that you used "sorry" instead
of a real value. In Lean "sorry" can be used instead
of an underscore to represent a placeholder. Give it
a try.
-/

#check n
#eval n

#check s
#eval s

#check b
#eval b

/-
Here's an important insight. In each of the three
little problems above, you had to *prove* that a
value of a specific type could be bound to a given
identifier. The values that you picked can thus be
though of as very simple proofs!

Not every type can be proved. For example, there is
a type called False that has n o proof (no values).
You can declare an identifier f to be bound to a
value of this type, and you can use a placeholder
to tell Lean to accept your definition, but you'll
never be able to fill in the placeholder because
there is no proof of the type, False. For extra
credit, declare the identifier F to be bound to a
proof of False, using a placeholder where the proof
(value) would go.
-/

/-
When you're done and there are no red underlines
in the logic/code we've provided to you, you may
submit your file. (If you did the extra credit of
course there will be a red squiggle under where a
value of type False is expected.)
-/
