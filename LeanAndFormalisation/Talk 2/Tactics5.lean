module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Tactic.ApplyAt

/-!
## Groups in Lean

In this sheet we will see some basic results about (multiplicative) groups.
The main goal is to show that `1⁻¹ = 1`, where `1 : G` is the identity
element.

-/

public section

/-

## Tactic sheet

`rfl` :: used to prove `a = a` or `P ↔ P`
`exact` :: used to give the precise proof term
`apply` :: used to simplify/update the goal or a proof term (using `at`)
`rw []` :: used to rewrite terms in the goal or in a proof term (using `at`)
`intro` :: used to introduce terms

-/

#check mul_assoc
#check one_mul
#check inv_mul_cancel
#check mul_inv_cancel

lemma mul_left {G : Type} [Group G] (a b c : G) : b = c → a * b = a * c := by
  sorry

lemma mul_left_cancel' {G : Type} [Group G] (a b c : G) : a * b = a * c → b = c := by
  sorry

#check mul_left_cancel

lemma inv_eq_of_mul_eq_one_right' {G : Type} [Group G] {a b : G} : a * b = 1 → a⁻¹ = b := by
  sorry

#check inv_eq_of_mul_eq_one_right

theorem one_inv (G : Type) [Group G] : (1 : G)⁻¹ = 1 := by
  sorry
