/-!
Tests the deprecated multi-location form of `rwa` (`rwa [rules] at h₁ h₂`, `at *`, `at ⊢`), and the
replacement its deprecation warning suggests. The non-deprecated forms of `rwa` are tested in
`tests/elab/rwa.lean`.
-/

-- Enabled to check the replacement suggested by the deprecation of this syntax.
set_option linter.deprecated.syntax true

section DeprecatedMultiLocation

variable {a b : α} {P Q R : α → Prop}

/--
warning: syntax 'Lean.Parser.Tactic.rwaAtLegacyLocation' has been deprecated: use `rw [...] at ... <;> assumption` instead

Hint: Replace the deprecated syntax:
  r̵w̵a̵(̲r̲w̲ [h] at ha hb hc ̲<̲;̲>̲ ̲a̲s̲s̲u̲m̲p̲t̲i̲o̲n̲)̲

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
-/
#guard_msgs in
example (ha : P a) (hb : Q a) (hc : R a) (h : a = b) : P b := by
  rwa [h] at ha hb hc

/--
warning: syntax 'Lean.Parser.Tactic.rwaAtLegacyLocation' has been deprecated: use `rw [...] at ... <;> assumption` instead

Hint: Replace the deprecated syntax:
  r̵w̵a̵(̲r̲w̲ [Nat.zero_add] at * ̲<̲;̲>̲ ̲a̲s̲s̲u̲m̲p̲t̲i̲o̲n̲)̲

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
-/
#guard_msgs in
example (S : Nat → Prop) (n : Nat) (h : S (0 + n)) : S n := by
  rwa [Nat.zero_add] at *

/--
warning: syntax 'Lean.Parser.Tactic.rwaAtLegacyLocation' has been deprecated: use `rw [...] at ... <;> assumption` instead

Hint: Replace the deprecated syntax:
  r̵w̵a̵(̲r̲w̲ [Nat.zero_add] at ⊢ ̲<̲;̲>̲ ̲a̲s̲s̲u̲m̲p̲t̲i̲o̲n̲)̲

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
-/
#guard_msgs in
example (S : Nat → Prop) (n : Nat) (h : S n) : S (0 + n) := by
  rwa [Nat.zero_add] at ⊢

/--
warning: syntax 'Lean.Parser.Tactic.rwaAtLegacyLocation' has been deprecated: use `rw [...] at ... <;> assumption` instead

Hint: Replace the deprecated syntax:
  r̵w̵a̵(̲r̲w̲ [h] at ha ⊢ ̲<̲;̲>̲ ̲a̲s̲s̲u̲m̲p̲t̲i̲o̲n̲)̲

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
-/
#guard_msgs in
example (ha : P a) (h : a = b) : P a := by
  rwa [h] at ha ⊢

end DeprecatedMultiLocation
