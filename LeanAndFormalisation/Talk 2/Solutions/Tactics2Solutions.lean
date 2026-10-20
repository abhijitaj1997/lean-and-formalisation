module

public import Mathlib.Algebra.Group.Nat.Defs

/-!
## Solutions to Tactics 2

-/

public section

/-
## Using and expanding the library
-/

example (a b c d : ℕ) : a + b + c + d = a + (b + (c + d)) := by
  rw [Nat.add_assoc, Nat.add_assoc]

example (a b c d : ℕ) : a + b + c + d = (b + (c + d)) + a := by
  rw [add_assoc, add_assoc, add_comm]

example (P : Prop) (a b c d : ℕ) (hP : P) (h : P → a + b ≤ 0) (hac : a = c) (hdb : d = b) :
    d + c ≤ 0 := by
  rw [hdb, ← hac, Nat.add_comm]
  apply h
  exact hP

example (a b c d : ℕ) : (a + b) + (c + d) = (d + c) + (a + b) := by
  rw [Nat.add_comm, Nat.add_comm c d]

example (a b c d : ℕ) (hcd : c = d) : a + b + c = b + a + d := by
  rw [Nat.add_comm a b, hcd]

def next : (ℕ → ℕ) := fun n ↦ (n + 1)

lemma add_next (a b : ℕ) : a + next b = next (a + b) := by
  simp only [next]
  rw [Nat.add_assoc]

example (a b c d : ℕ) : a + (b + (c + next d)) = next (a + b + c + d) := by
  rw [add_next, add_next, add_next, ← Nat.add_assoc, ← Nat.add_assoc]
