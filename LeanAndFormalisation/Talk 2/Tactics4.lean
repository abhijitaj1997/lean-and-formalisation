module

public import Mathlib

/-!
## Standard number systems

In this sheet we shall try and solve some basic arithmetic regarding the
real numbers.

-/

public section

/-
## The tactics `linarith` and `norm_num`

The tactic `linarith` can be used to solve linear equations about certain
semirings like `ℕ`, `ℤ` and `ℚ`. The second tactic, `norm_num` is lean's
calculator tactic. It can also solve linear equations in a manner similar
to linarith
-/

example : 1 + 1 = 2 := by
  linarith

example : 1 + 1 = 2 := by
  norm_num

example : 1 + 5 < 7 := by
  sorry

example : (6 : ℚ) * 2 = 12 := by
  sorry

example : ¬ (1 + 2 > 5) := by
  sorry

example : (6 : ℤ) * 2 + 1 ≠ 18 := by
  sorry

def ten := 10
example : 2 * 5 = ten := by
  sorry

example (n : ℕ) : 0 ≤ n := by
  sorry

/-
`linarith` also has the ability to solve the goal using the assumptions
-/

example (n : ℕ) (hn : n ≤ 5) : n < 10 := by
  sorry

example (m n : ℕ) (hm : m < 3) (hn : n < 2) : m + n < 5 := by
  sorry

example : ∀ m n : ℕ, m = 3 → n > 5 → 5 * m + n > 20 := by
  sorry

/-
## The `use` tactic

The tactic `use` can be used to solve goals which start with a `∃`. Like
`rw`, the tactic `use` also immediately solves goals like `x = x`.
-/

example : ∃ x : ℝ, x = 1 := by
  use 1

example : ∃ y : ℚ, y ^ 3 = 27 / 8 := by
  sorry

def eight : ℕ := 8
example : ∃ n : ℕ, n * 2 = eight := by
  sorry

/-
If you want to `use a` followed by `use b`, you can do that in a simple line
by typing `use a, b` - similar to `rw`.
-/

example : ∃ x₁ x₂ : ℝ, x₁ + x₂ = x₁ * x₂ := by
  sorry

example : ∃ x y : ℝ, x + y = 5 ∧ 3 * x - 2 * y = 0 := by
  sorry
