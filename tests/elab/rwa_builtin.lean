module

import Init.Tactics

/-!
# Builtin `rwa` elaboration

Tests that the builtin `rwa` elaborator is preferred to its bootstrap macro even when
`Lean.Elab.Tactic.Rwa` is not imported.
-/

set_option linter.unnecessaryRwa true
set_option linter.deprecated.syntax true

/--
warning: `rw` already closes the goal

Hint: Use `rw` instead of `rwa`:
  [apply] rw [h]

Note: This linter can be disabled with `set_option linter.unnecessaryRwa false`
-/
#guard_msgs in
example (h : n = m) : n = m := by
  rwa [h]

/--
warning: `rw` already closes the goal

Hint: Use `rw` instead of `rwa`:
  [apply] rw [h] at ha

Note: This linter can be disabled with `set_option linter.unnecessaryRwa false`
-/
#guard_msgs in
set_option linter.unusedVariables false in
example (a b : Nat) (ha : a = 0) (h : a = b) : (0 : Nat) = 0 := by
  rwa [h] at ha

/--
warning: syntax 'Lean.Parser.Tactic.rwaAtLegacyLocation' has been deprecated: use `rw [...] at ... <;> assumption` instead

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
-/
#guard_msgs in
example {a b : α} {P Q : α → Prop} (ha : P a) (_hb : Q a) (h : a = b) : P b := by
  rwa [h] at ha _hb
