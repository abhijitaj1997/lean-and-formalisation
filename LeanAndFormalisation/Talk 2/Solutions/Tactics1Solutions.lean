module

public import Mathlib.Data.Real.Basic

/-!
## Solutions to Tactics 1

-/

public section

/-
## the `rfl` tactic
-/

example : 1 = 1 := by
  rfl

example (a : ℕ) : a = a := by
  rfl

example (a b : ℝ) : a + b = a + b := by
  rfl

example (P : Prop) : P ↔ P := by
  rfl

example (P Q : Prop) : P ∧ Q ↔ P ∧ Q := by
  rfl

example (P : Prop) (h₁ h₂ : P) : h₁ = h₂ := by
  rfl

def five₀ : ℕ := 5
def five₁ : ℕ := 5

example : five₀ = 5 := by
  rfl

example : five₀ = five₁ := by
  rfl

/-
## the `exact` tactic
-/

example (P : Prop) (h : P) : P := by
  exact h

example (P Q : Prop) (hP : P) (hPQ : P → Q) : Q := by
  exact hPQ hP

example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := by
  constructor
  · exact hP
  · exact hQ

/-
## the `apply` tactic
-/

example (P Q : Prop) (hP : P) (hPQ : P → Q) : Q := by
  apply hPQ
  exact hP

example (P Q R S : Prop) (hPQ : P → Q) (hQR : Q → R) (hRS : R → S) (hP : P) : S := by
  apply hRS
  apply hQR
  apply hPQ
  exact hP

-- using `at`
example (P Q R S : Prop) (hPQ : P → Q) (hQR : Q → R) (hRS : R → S) (hP : P) : S := by
  apply hPQ at hP
  apply hQR at hP
  apply hRS at hP
  exact hP

/-
## the `rw` tactic
-/

example (a b c : ℕ) (h₁ : a = b) (h₂ : b = c) : a ^ 2 = c ^ 2 := by
  rw [h₁, h₂]

example (a b c : ℕ) (hca : c = a) (hcb : c = b) : a = b := by
  rw [← hca, hcb]

-- using `at`
example (a b c : ℕ) (hca : c = a) (hcb : c = b) : a = b := by
  rw [hca] at hcb
  exact hcb

/-
## the `intro` tactic
-/

example (P Q : Prop) : P → ((P → Q) → Q) := by
  intro hP hPQ
  apply hPQ
  exact hP

example : ∀ n m : ℕ, m = n → n + m = n + n := by
  intro n m h
  rw [h]
