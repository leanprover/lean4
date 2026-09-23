import Std.Tactic.Do

/-!
Tests that each call of a `Std.Do` proof mode tactic reports one deprecation warning, including
calls whose expansion uses further proof mode tactics.
-/

open Std.Do
set_option linter.deprecated.syntax true

/--
warning: syntax 'Lean.Parser.Tactic.mintro' has been deprecated: the `Std.Do` proof mode is deprecated; use `vcgen` from `Std.Tactic.WP`

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
---
warning: syntax 'Lean.Parser.Tactic.mexact' has been deprecated: the `Std.Do` proof mode is deprecated; use `vcgen` from `Std.Tactic.WP`

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
-/
#guard_msgs in
example (P Q R : SPred []) : ⊢ₛ P → Q → R → P := by
  mintro hp hq hr
  mexact hp

/--
warning: syntax 'Lean.Parser.Tactic.mintro' has been deprecated: the `Std.Do` proof mode is deprecated; use `vcgen` from `Std.Tactic.WP`

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
---
warning: syntax 'Lean.Parser.Tactic.mexists' has been deprecated: the `Std.Do` proof mode is deprecated; use `vcgen` from `Std.Tactic.WP`

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
-/
#guard_msgs in
example (ψ : Nat → SPred []) : ψ 42 ⊢ₛ ∃ x, ψ x := by
  mintro h
  mexists 42

def prog : StateM Nat Unit := modify (· + 1)

/--
warning: syntax 'Lean.Parser.Tactic.mvcgen' has been deprecated: use `vcgen` instead

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
-/
#guard_msgs in
example : ⦃fun s => ⌜s = 0⌝⦄ prog ⦃⇓ _ s => ⌜s = 1⌝⦄ := by
  mvcgen [prog] with grind
