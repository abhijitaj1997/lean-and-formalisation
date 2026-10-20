module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Tactic.ApplyAt

/-!
## Solutions to Tactics 5

-/

public section

/-
## Groups in Lean
-/

lemma mul_left {G : Type} [Group G] (a b c : G) : b = c → a * b = a * c := by
  intro h
  rw [h]

lemma mul_left_cancel' {G : Type} [Group G] (a b c : G) : a * b = a * c → b = c := by
  intro h
  apply mul_left a⁻¹ at h
  rw [← mul_assoc, ← mul_assoc, inv_mul_cancel, one_mul, one_mul] at h
  exact h

lemma inv_eq_of_mul_eq_one_left' {G : Type} [Group G] {a b : G} : a * b = 1 → a⁻¹ = b := by
  intro h
  apply mul_left_cancel' a
  rw [mul_inv_cancel, h]

theorem one_inv (G : Type) [Group G] : (1 : G)⁻¹ = 1 := by
  apply inv_eq_of_mul_eq_one_left'
  rw [one_mul]
