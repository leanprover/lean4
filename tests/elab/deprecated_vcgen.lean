import Std.WP

/-!
Tests that `vcgen` reports deprecated theorems it uses as specs once, does not report erased
specs, and leaves reporting the theorems it passes on to `simp` to `simp`.
-/

set_option linter.deprecated true
set_option experimental.vcgen true

open Std.WP Lean.Order

def sumDef (l : List Nat) : Nat := Id.run do
  let mut acc := 0
  for x in l do acc := acc + x
  return acc

theorem replacementThm (n : Nat) : n + 0 = n := rfl
@[deprecated replacementThm (since := "2025-01-01")] theorem deprecatedThm (n : Nat) : n + 0 = n := rfl
-- Deprecated theorems should not be tagged with `[simp]`, but the test needs such a theorem.
set_option linter.deprecated false in
@[simp, deprecated replacementThm (since := "2025-01-01")]
theorem deprecatedSimpThm (n : Nat) : n + 0 = n := rfl

-- A deprecated simp lemma is reported once, by `simp`.
/--
warning: `deprecatedThm` has been deprecated: Use `replacementThm` instead

Hint: Replace the deprecated name:
  d̵e̵p̵r̵e̵c̵a̵t̵e̵d̵T̵h̵m̵r̲e̲p̲l̲a̲c̲e̲m̲e̲n̲t̲T̲h̲m̲
-/
#guard_msgs in
theorem sumDef_eq (l : List Nat) : sumDef l = l.sum := by
  generalize h : sumDef l = r
  apply Id.of_run_eq_wp h
  vcgen [sumDef, deprecatedThm] invariants
  · fun _pref suff acc => ⌜acc + suff.sum = l.sum⌝
  with finish

def programDef : Id Nat := pure 3

@[spec] theorem replacementSpecThm : ⦃True⦄ programDef ⦃fun r => r = 3⦄ := by
  vcgen [programDef]
@[spec, deprecated replacementSpecThm (since := "2025-01-01")]
theorem deprecatedSpecThm : ⦃True⦄ programDef ⦃fun r => r = 3⦄ := replacementSpecThm

def callerDef : Id Nat := programDef

/--
warning: `deprecatedSpecThm` has been deprecated: Use `replacementSpecThm` instead

Hint: Replace the deprecated name:
  d̵e̵p̵r̵e̵c̵a̵t̵e̵d̵S̵p̵e̵c̵T̵h̵m̵r̲e̲p̲l̲a̲c̲e̲m̲e̲n̲t̲S̲p̲e̲c̲T̲h̲m̲
-/
#guard_msgs in
theorem callerDef_spec : ⦃True⦄ callerDef ⦃fun r => r = 3⦄ := by
  vcgen [callerDef, deprecatedSpecThm]

-- Erasing a deprecated spec is not reported, since it can only be erased by its name.
#guard_msgs in
theorem callerDef_spec' : ⦃True⦄ callerDef ⦃fun r => r = 3⦄ := by
  vcgen [callerDef, programDef, -deprecatedSpecThm]

-- Erasing a deprecated simp lemma is not reported either.
#guard_msgs in
theorem sumDef_eq' (l : List Nat) : sumDef l = l.sum := by
  generalize h : sumDef l = r
  apply Id.of_run_eq_wp h
  vcgen [sumDef, -deprecatedSimpThm] invariants
  · fun _pref suff acc => ⌜acc + suff.sum = l.sum⌝
  with finish
