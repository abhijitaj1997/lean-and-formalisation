module

public import Mathlib.Algebra.Group.Nat.Defs

/-!
## Solutions to Tactics 3

-/

public section

/-
## The `constructor` tactic
-/

lemma and_comm' {P Q : Prop} : P ∧ Q → Q ∧ P := by
  intro h
  constructor
  · exact h.2
  · exact h.1

example (P Q : Prop) : P ∧ Q ↔ Q ∧ P := by
  constructor
  · exact and_comm'
  · exact and_comm'

example (P Q R : Prop) : ((P → Q) ∧ (P → R)) → (P → Q ∧ R) := by
  intro h hP
  constructor
  · apply h.1
    exact hP
  · apply h.2
    exact hP

example (P Q R S : Prop) (h : S ∧ P ∧ Q ∧ R) : R ∧ Q ∧ P ∧ S := by
  constructor
  · exact h.2.2.2
  · constructor
    · exact h.2.2.1
    · constructor
      · exact h.2.1
      · exact h.1

/-
## The `left` and `right` tactics
-/

example (P Q R S T : Prop) (hR : R) : P ∨ ((Q ∨ (R ∨ S)) ∨ T) := by
  right
  left
  right
  left
  exact hR

lemma or_comm' {R S : Prop} : R ∨ S → S ∨ R := by
  intro h
  rcases h with (hl | hr)
  · right
    exact hl
  · left
    exact hr

example (P Q : Prop) : P ∨ Q ↔ Q ∨ P := by
  constructor
  · exact or_comm'
  · exact or_comm'

example (P Q R : Prop) : P ∧ (Q ∨ R) → (P ∧ Q) ∨ (P ∧ R) := by
  intro h
  rcases h.2 with (hl | hr)
  · left
    constructor
    · exact h.1
    · exact hl
  · right
    constructor
    · exact h.1
    · exact hr

example (P Q R : Prop) : P ∨ (Q ∧ R) → (P ∨ Q) ∧ (P ∨ R) := by
  intro h
  rcases h with (hl | hr)
  · constructor
    · left
      exact hl
    · left
      exact hl
  · constructor
    · right
      exact hr.1
    · right
      exact hr.2
