import Std.Tactic.Do

open Std.Do

set_option mvcgen.warning false

def foo (x : Id Nat → Id Nat) : Id Nat := do
  let r₁ ← x (pure 42)
  let r₂ ← x (pure 26)
  pure (r₁ + r₂)

theorem foo_spec
    (x : Id Nat → Id Nat)
    (x_spec : ∀ (k : Id Nat) (_ : ⦃⌜True⌝⦄ k ⦃⇓r => ⌜r % 2 = 0⌝⦄), ⦃⌜True⌝⦄ x k ⦃⇓r => ⌜r % 2 = 0⌝⦄) :
    ⦃⌜True⌝⦄ foo x ⦃⇓r => ⌜r % 2 = 0⌝⦄ := by
  mvcgen [foo, x_spec] <;> grind

def bar (k : Id Nat) : Id Nat := do
  let r ← k
  if r > 30 then return 12 else return r

example : ⦃⌜True⌝⦄ foo bar ⦃⇓r => ⌜r % 2 = 0⌝⦄ := by
  mvcgen [foo_spec, bar] -- unfold `bar` and automatically apply the spec for the higher-order argument `k`
