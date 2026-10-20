module

public import Mathlib.Algebra.Group.Nat.Defs

/-!
## Using and expanding the library

When trying to prove a result, apart from the hypotheses you have assumed, you can also
access results that have been verified and put into `Mathlib`. Below, put your cursor
anywhere on a `#check` command to see what type the terms have.
-/

public section

#check Nat.add_comm
#check Nat.add_assoc

example (n m : ℕ) : n + m = m + n := by
  rw [Nat.add_comm]

example (a b c d : ℕ) : a + b + c + d = a + (b + (c + d)) := by
  sorry

example (a b c d : ℕ) : a + b + c + d = (b + (c + d)) + a := by
  sorry

example (P : Prop) (a b c d : ℕ) (hP : P) (h : P → a + b ≤ 0) (hac : a = c) (hdb : d = b) :
    d + c ≤ 0 := by
  sorry

/-
Sometimes it is important to specify which term you are applying your proof to
rather than let Lean guess it.

Suppose we have a goal `A + B = C + D`. Then, `rw [Nat.add_comm]` finds the very
first, and outermost `+`, which is `A + B` here, and rewrites that to `B + A`
*everywhere* in the equation. But, if we want to rewrite another `+` using commutativity,
like `C + D` here, then we need to use `rw [Nat.add_comm C D]`.

Try to use this in the next two examples.
-/

example (a b c d : ℕ) : (a + b) + (c + d) = (d + c) + (a + b) := by
  sorry

example (a b c d : ℕ) (hcd : c = d) : a + b + c = b + a + d := by
  sorry

/-
In a manner similar to how we have used proofs from `Mathlib`, we are also allowed
to define new terms, and use them locally in our file. To do this, it is
important that we give these terms a name.
-/

def next : (ℕ → ℕ) := fun n ↦ (n + 1)

lemma add_next (a b : ℕ) : a + next b = next (a + b) := by
  -- `simp only [next]` unfolds the definition of `next`
  simp only [next]
  sorry

-- Solve this by only changing the LHS.
example (a b c d : ℕ) : a + (b + (c + next d)) = next (a + b + c + d) := by
  sorry
