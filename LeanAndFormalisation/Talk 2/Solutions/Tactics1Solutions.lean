module

public import Mathlib.Basic.Real.Basic

/-!
## Solutions to Tactics 1

-/

public section

/-
## The `rfl` tactic
-/

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
## The `exact` tactic
-/

example (P Q R : Prop) (a_name : P) (a_new_name : Q) (another_new_name : R) : P := by
  exact a_name

example (P Q : Prop) (hP : P) (hPQ : P → Q) : Q := by
  exact hPQ hP

example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := by
  exact ⟨hP, hQ⟩

/-
## The `apply` tactic
-/

example (P Q R S : Prop) (hPQ : P → Q) (hQR : Q → R) (hRS : R → S) (hP : P) : S := by
  apply hRS
  apply hQR
  apply hPQ
  exact hP

example (P : Prop) (hP : P) (h_danger : P → 1 < 0) : 1 < 0 := by
  apply h_danger
  exact hP

def six := 6
example (P : Prop) (h : six = 6 → P) : P := by
  apply h
  rfl

-- using `apply ... at ...`

example (P : Prop) (hP : P) (h_danger : P → 1 < 0) : 1 < 0 := by
  apply h_danger at hP
  exact hP

example (P Q R S : Prop) (hPQ : P → Q) (hQR : Q → R) (hRS : R → S) (hP : P) : S := by
  apply hPQ at hP
  apply hQR at hP
  apply hRS at hP
  exact hP

/-
## The `rw` tactic
-/

example (a b c d : ℕ) (h₁ : a = b) (h₂ : b = c) (h₃ : c = d) : a ^ 2 = d ^ 2 := by
  rw [h₁, h₂, h₃]

def one := 2
example (two : ℕ) (P : Prop) (ht : two = 2) (h : one = two → P) : P := by
  apply h
  rw [ht]
  rfl

example (a b c : ℕ) (hca : c = a) (hcb : c = b) : a = b := by
  rw [← hca, hcb]

example (P Q R S : Prop) (hPQ : P ↔ Q) (hRQ : R ↔ Q) (hSR : S ↔ R) : P ↔ S := by
  rw [hPQ, ← hRQ, hSR]

-- using `rw [...] at ...`

example (a b c : ℕ) (hca : c = a) (hcb : c = b) : a = b := by
  rw [hca] at hcb
  exact hcb

example (P Q R S : Prop) (hPQ : P ↔ Q) (hRQ : R ↔ Q) (hSR : S ↔ R) : P ↔ S := by
  rw [hRQ, ← hPQ] at hSR
  rw [hSR]

/-
## The `intro` tactic
-/

example (P : Prop) : P → P := by
  intro hP
  exact hP

example (P Q : Prop) (hQ : Q) : P → Q := by
  intro hP
  exact hQ

example (P Q R : Prop) : P → (P → Q) → R → P := by
  intro hP hPQ hR
  exact hP

example (P Q : Prop) : P → ((P → Q) → Q) := by
  intro hP hPQ
  apply hPQ
  exact hP

example (P Q R S : Prop) : (P → Q) → (R ↔ P) → (Q → S) → (R → S) := by
  intro hPQ hRP hQS hR
  apply hQS
  apply hPQ
  rw [← hRP]
  exact hR

example (P Q : Prop) : (((P → Q) → Q) → Q) → P → Q := by
  intro h hP
  apply h
  intro hPQ
  apply hPQ
  exact hP

example : ∀ n m : ℕ, m = n → n + m = n + n := by
  intro n m hmn
  rw [hmn]
