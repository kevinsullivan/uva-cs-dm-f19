import ..src.mbox

open boxed

/-
What we'd *really* like to know is that
∀ (α : Type), ∀ (t : α), unbox (box t) = t.
Your assignment here is to test that this
proposition is true when applied to a few
specific cases, e.g., where t=3, t=tt, and
t="Hi There".
-/

#eval unbox (box 3)
#eval unbox (box "Hi there")
#eval unbox (box tt)



