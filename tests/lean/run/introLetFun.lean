import Lean.Elab.Tactic.Basic
import Lean.Meta.Tactic.Intro
/-!
# Testing `intro` with `letFun`
-/

/-!
Explicit `intro`.
-/
example : have x := 2; ∀ _ : Nat, x = x := by
  intro x _
  rfl

/-!
`intros` is aware of `letFun`.
-/
example : have x := 2; ∀ _ : Nat, x = x := by
  intros
  rfl

/-!
Check that it works for `letFun` with an eta reduced argument.
-/
example (p : Nat → Prop) (h : ∀ x, p x) : letFun 2 p := by
  intro
  apply h
