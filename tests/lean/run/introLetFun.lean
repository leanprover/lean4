import Lean.Elab.Tactic.Basic
import Lean.Meta.Tactic.Intro
/-!
# Testing `intro` with `have`
-/

/-!
Explicit `intro`.
-/
example : have x := 2; ∀ _ : Nat, x = x := by
  intro x _
  rfl

/-!
`intros` is aware of `have`.
-/
example : have x := 2; ∀ _ : Nat, x = x := by
  intros
  rfl
