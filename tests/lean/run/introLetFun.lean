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
Check that the default name for `letFun` with an eta reduced argument is usable.
When the name is anonymous, it uses `a` for the name.
-/
elab "introp" : tactic => Lean.Elab.Tactic.liftMetaTactic fun g => do
  ([·]) <$> Prod.snd <$> g.intro1P

example (p : Nat → Prop) (h : ∀ x, p x) : letFun 2 p := by
  introp
  exact h a
