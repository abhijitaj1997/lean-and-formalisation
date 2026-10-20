module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Ineq

/-!
## Solutions to Tactics 4

-/

public section

/-
## The tactics `linarith` and `norm_num`
-/

-- `norm_num` also works
example : 1 + 5 < 7 := by
  linarith

-- `norm_num` also works
example : (6 : ℚ) * 2 = 12 := by
  linarith

-- `norm_num` also works
example : ¬ ((1 : ℝ) + 2 > 5) := by
  linarith

-- `norm_num` also works
example : (6 : ℤ) * 2 + 1 ≠ 18 := by
  linarith

def ten := 10
example : 2 * 5 = ten := by
  norm_num
  rfl

example (n : ℕ) : n + n = 2 * n := by
  linarith

-- `norm_num` also works
example (n : ℕ) : 0 ≤ n := by
  linarith

example (n : ℕ) (hn : n ≤ 5) : n < 10 := by
  linarith

example (m n : ℕ) (hm : m < 3) (hn : n < 2) : m + n < 5 := by
  linarith

example : ∀ m n : ℕ, m = 3 → n > 5 → 5 * m + n > 20 := by
  intro m n hm hn
  linarith

/-
## The `use` tactic
-/

-- `norm_num` also works
example : ∃ y : ℚ, y ^ 3 = 27 / 8 := by
  use 3 / 2
  linarith

def eight : ℕ := 8
example : ∃ n : ℕ, n * 2 = eight := by
  use 4
  norm_num
  rfl

-- `norm_num` also works
example : ∃ x₁ x₂ : ℝ, x₁ + x₂ = x₁ * x₂ := by
  use 2, 2
  linarith

example : ∃ x y : ℝ, x + y = 5 ∧ 3 * x - 2 * y = 0 := by
  use 2, 3
  norm_num
