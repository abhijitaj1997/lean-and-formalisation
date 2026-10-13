module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Prime.Defs

/-!
## Examples

This Lean file contains all the examples discussed in the slides.

-/

public section

-- Examples of propositions
#check 1 ≤ 2
#check 2 + 2 = 5
#check ∀ x : ℕ, 0 ≤ x
#check ∀ n : ℕ, (∃ a b c : ℕ, a ^ n + b ^ n = c ^ n) → n ≤ 2
#check ∀ n : ℕ, ∀ x y : ℝ, ¬ (2 ∣ n) → x ^ n = y ^ n → x = y

-- Example 1
example (P : Prop) (h : P) : P :=
  h


-- Example 2
example (P Q : Prop) (hPQ : P → Q) (hP : P) : Q :=
  hPQ hP


-- Example 3
example (P Q R S : Prop) (hPQ : P → Q) (hQR : Q → R) (hRS : R → S) (hP : P) : S :=
  hRS (hQR (hPQ hP))


-- Example 4
example (P Q R S : Prop) (hPQ : P → Q) (hQR : Q → R) (hRS : R → S) : P → S :=
  fun (hP : P) ↦ hRS (hQR (hPQ hP))


-- Example 5
example (n : ℕ) (hypo : n ≥ 53 → n > 50) (h : n > 47 ∧ Nat.Prime n → n ≥ 53)
    (h₁ : n > 47) (h₂ : Nat.Prime n) : n > 50 :=
  hypo (h ⟨h₁, h₂⟩)

-- Interesting example
example {G : Type} [Group G] : (1 : G)⁻¹ = 1 :=
  have this := fun {a b} h ↦
    have this' :=
      Eq.mpr (id (congrArg (fun _a ↦ a⁻¹ * a * b = a⁻¹ * _a) (Eq.symm h)))
        (Eq.mpr (id (congrArg (fun _a ↦ _a = a⁻¹ * (a * b)) (mul_assoc a⁻¹ a b))) (Eq.refl (a⁻¹ *
        (a * b))));
    Eq.mpr
      (id
        (congrArg (fun _a ↦ a⁻¹ = _a)
          (Eq.mp (congrArg (fun _a ↦ b = _a) (mul_one a⁻¹))
            (Eq.mp (congrArg (fun _a ↦ _a = a⁻¹ * 1) (one_mul b))
              (Eq.mp (congrArg (fun _a ↦ _a * b = a⁻¹ * (1 : G)) (inv_mul_cancel a)) this')))))
      (Eq.refl a⁻¹);
  this (Eq.mpr (id (congrArg (fun _a ↦ _a = 1) (one_mul 1))) (Eq.refl 1))

-- Example 2 using tactics
example (P Q : Prop) (hPQ : P → Q) (hP : P) : Q := by
  apply hPQ
  exact hP
