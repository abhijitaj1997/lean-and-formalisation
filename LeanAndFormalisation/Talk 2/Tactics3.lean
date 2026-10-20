module

public import Mathlib.Tactic.Lemma

/-!
## `And` and `Or` proofs

In this sheet, we shall see how to prove `And` and `Or` statements.

-/

public section

/-
## The `constructor` tactic

To prove an `And` statement, you can use the `constructor` tactic, which breaks the
one goal that you have into two goals. It is good practice to indent your new goals
using the character `·` (which you can get by typing `\.`). Have a look at the first
example and try the others yourself.
-/

example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := by
  constructor
  · exact hP
  · exact hQ

/-
Note that if `P Q : Prop` and `h : P ∧ Q`, then `h.1 : P` and `h.2 : Q`.
Also, note that `↔` is also an `And` statement.
-/

-- you get `·` by typing `\.` or `\dot`.
lemma and_comm' {R S : Prop} : R ∧ S → S ∧ R := by
  sorry

example (P Q : Prop) : P ∧ Q ↔ Q ∧ P := by
  sorry

example (P Q R : Prop) : ((P → Q) ∧ (P → R)) → (P → Q ∧ R) := by
  sorry

example (P Q R S : Prop) (h : S ∧ P ∧ Q ∧ R) : R ∧ Q ∧ P ∧ S := by
  sorry
















/-
## The `left` and `right` tactics

To prove an `Or` statement, you can choose whether you wish to prove the left side
or the right side of the statement using the keywords `left` and `right`
respectively.

Have a look at the next two examples and try the remaining ones yourself.
-/

example (P Q : Prop) (hP : P) : P ∨ Q := by
  left
  exact hP

example (P Q : Prop) (hQ : Q) : P ∨ Q := by
  right
  exact hQ

example (P Q R S T : Prop) (hR : R) : P ∨ ((Q ∨ (R ∨ S)) ∨ T) := by
  sorry

lemma or_comm' {R S : Prop} : R ∨ S → S ∨ R := by
  intro h
  rcases h with (hl | hr)
  · sorry
  · sorry

example (P Q : Prop) : P ∨ Q ↔ Q ∨ P := by
  sorry

example (P Q R : Prop) : P ∧ (Q ∨ R) → (P ∧ Q) ∨ (P ∧ R) := by
  intro h
  rcases h.2 with (hl | hr)
  · sorry
  · sorry

example (P Q R : Prop) : P ∨ (Q ∧ R) → (P ∨ Q) ∧ (P ∨ R) := by
  intro h
  rcases h with (hl | hr)
  · sorry
  · sorry
