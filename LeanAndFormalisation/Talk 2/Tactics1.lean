module

public import Mathlib.Basic.Real.Basic

/-!
## Tactics

In this file we will explore the tactics `rfl`, `exact`, `apply`, `rw`
and `intro` - the five most basic tactics.

-/

public section

/-
## Switching to tactic mode

Before we move forward, I should introduce the keyword `sorry`. This keyword can be
used wherever Lean expects a term — for instance, in a `def`, `theorem`, `lemma` or
`example`. After the `:=`, Lean is waiting for you to give it the term. But, if you are
unable to give the term, and just leave it blank, Lean will give you an error. So,
`sorry` is basically us telling Lean, 'sorry, I know that I have not given you the term,
but please do not give me an error'.

We have seen in the slides that providing the proof term is not always easy - instead
we use tactics. By default Lean is looking for a proof term. To tell Lean that we
will prove a statement using tactics instead of a proof term, we need to switch to
tactic mode. This is done by adding the keyword `by` in between `:=` and `sorry`.
-/

-- Lean is expecting you to give a proof term
example : ∀ n : ℕ, 0 ≤ n :=
  sorry

-- Lean is expecting you to prove this using tactics
example : ∀ n : ℕ, 0 ≤ n := by
  sorry










/-
## The `rfl` tactic

`rfl` is short for reflexivity. There are two main scenarios you use it in: `=` and
`↔`. Basically, if you are supposed to provide a proof of the statement `a = a` or
`P ↔ P`, you can use this tactic.
-/

example : 1 = 1 := by
  rfl

example (a : ℕ) : a = a := by
  sorry

example (a b : ℝ) : a + b = a + b := by
  sorry

example (P : Prop) : P ↔ P := by
  sorry

example (P Q : Prop) : P ∧ Q ↔ P ∧ Q := by
  sorry

example (P : Prop) (h₁ h₂ : P) : h₁ = h₂ := by
  sorry

-- `rfl` will not work for this next one. Why?
example (a b c : ℕ) : (a + b) + c = a + (b + c) := by
  sorry

-- `rfl` also works if two things are definitionally equal
def five₀ : ℕ := 5
def five₁ : ℕ := 5

example : five₀ = 5 := by
  sorry

example : five₀ = five₁ := by
  sorry

/-
Note: `rfl` does not always require tactic mode. But, we shall not discuss that here.










## The `exact` tactic

As you can see, `rfl` only works if the exact same thing is written on both sides.
This means that it does not work for some very basic equalities (as seen above). But,
you should be able to fix that by the end of this lecture.

In the same way that `by` tells Lean that you are going from term mode to tactic mode,
the keyword `exact` tells Lean that you are going from tactic mode to term mode. Why
would you want to do that? Suppose, after multiple steps in a proof, you realise that
one of your hypotheses is exactly the goal. Since you have a term of this type, why
would you sit and prove it again? You can just tell Lean, "here look, I already have a
term of this type". But, as long as you are in tactic mode, just writing the term down
will give you an error. So, you switch back to term mode using `exact`, and then give
the term.

Have a look at the example below.
-/

example (P : Prop) (h : P) : P := by
  exact h

example (P Q : Prop) (hP : P) (hPQ : P → Q) : Q := by
  sorry

example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := by
  constructor
  · sorry
  · sorry










/-
## The `apply` tactic

Since both `rfl` and `exact` are supposed to finish the proof in a single line, there
are not many interesting exercises I can create with them. So, let's learn a new
tactic.

The tactic `apply` tells Lean to apply an implication to the goal and backtrack. Let
us try and understand that better. Consider example two from the slides. We want to
prove `Q`, assuming `P` and `P → Q` are true. We can tell Lean to apply the hypothesis
`hPQ`. Lean would then look at the target of the hypothesis, realise that it is `Q`,
and then ask you to prove `P` by going backwards in the function `P → Q`.
-/

example (P Q : Prop) (hP : P) (hPQ : P → Q) : Q := by
  apply hPQ
  exact hP

example (P Q R S : Prop) (hPQ : P → Q) (hQR : Q → R) (hRS : R → S) (hP : P) : S := by
  sorry

/-
Using the keyword `at`, we can also `apply` an implication to an existing proof
term. For instance, in the above example, if we have proof terms `hPQ : P → Q` and
`hP : P`, then we can use `apply hPQ at hP` to change `hP` into a term of type `Q`.
You can have a look at that example below, and also try and solve the second example
above using the `at` keyword.
-/


example (P Q : Prop) (hP : P) (hPQ : P → Q) : Q := by
  apply hPQ at hP
  exact hP

example (P Q R S : Prop) (hPQ : P → Q) (hQR : Q → R) (hRS : R → S) (hP : P) : S := by
  sorry










/-
## The `rw` tactic

Suppose we have a proof term `h` whose type resembles something of the form `a = b`.
Then, if there are any `a`s in the goal, `rw [h]` will replace them with `b`s.

Additionally, if `rfl` will finish the proof, Lean will automatically apply it.
-/

example (a b c : ℕ) (h₁ : a = b) (h₂ : b = c) : a ^ 2 = c ^ 2 := by
  rw [h₁]
  rw [h₂]

/-
`rw` can in fact take multiple arguments separated by commas. So, the above can be
solved in a single line using `rw [h₁, h₂]`. You can try it below.
-/

example (a b c : ℕ) (h₁ : a = b) (h₂ : b = c) : a ^ 2 = c ^ 2 := by
  sorry

/-
Consider the scenario where you have a proof term `h : c = b`, but you would like
to rewrite all the `b`s in your goal to `c`s. Unfortunately, `rw [h]` will not help
you achieve that. This is because `rw` replaces everything on the left of the
equality with everything on the right (and the same for `↔` statements). So, if you
would like to flip this around, you have to use the special character `←` (this is
achieved by typing `\l`). Try the following example.
-/

example (a b c : ℕ) (hca : c = a) (hcb : c = b) : a = b := by
  sorry

/-
We can also use the keyword `at` to rewrite existing proof terms. Just as with `apply`,
we need to write `rw [...] at h` if we would like to rewrite the proof term `h`.
Try the last example once more, but this time using the `at` keyword.
-/

example (a b c : ℕ) (hca : c = a) (hcb : c = b) : a = b := by
  sorry










/-
## The `intro` tactic

Often when we want to prove `P → Q`, we assume `P` is true and try to prove `Q`.
As discussed before, assuming `P` is true is the same as introducing an arbitrary proof
term of `P`, and then trying to find a proof term of `Q`. But this is also what we do
when we want to define a function `f : X → Y`, i.e., we introduce an arbitrary term, say
`x : X`, and determine a term of type `Y`, which we go on to call `f x : Y`. In Lean
we can do both these things using the `intro` tactic.
-/

example (P Q R : Prop) (hPQ : P → Q) (hQR : Q → R) : P → R := by
  intro hP
  apply hQR
  apply hPQ
  exact hP

/-
You can introduce multiple terms using a single intro command. The newly introduced
terms should be separated by a space. Try the example below.
-/

example (P Q : Prop) : P → ((P → Q) → Q) := by
  sorry

example : ∀ n m : ℕ, m = n → n + m = n + n := by
  sorry
