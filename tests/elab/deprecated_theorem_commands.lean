/-!
Tests that commands taking the name of a theorem (`#discr_tree_key`, `grind_pattern`,
`norm_cast_add_elim`, and `#grind_lint mute`/`skip`) report deprecated theorems.
-/

set_option linter.deprecated true

def replacementDef (n : Nat) : Nat := n + 1

theorem replacementThm (n : Nat) : replacementDef n = n + 1 := rfl
@[deprecated replacementThm (since := "2025-01-01")]
theorem deprecatedThm (n : Nat) : replacementDef n = n + 1 := rfl

/--
warning: `deprecatedThm` has been deprecated: Use `replacementThm` instead

Hint: Replace the deprecated name:
  d̵e̵p̵r̵e̵c̵a̵t̵e̵d̵T̵h̵m̵r̲e̲p̲l̲a̲c̲e̲m̲e̲n̲t̲T̲h̲m̲
---
info: @Eq Nat (replacementDef _) _
-/
#guard_msgs in
#discr_tree_key deprecatedThm

/--
warning: `deprecatedThm` has been deprecated: Use `replacementThm` instead

Hint: Replace the deprecated name:
  d̵e̵p̵r̵e̵c̵a̵t̵e̵d̵T̵h̵m̵r̲e̲p̲l̲a̲c̲e̲m̲e̲n̲t̲T̲h̲m̲
-/
#guard_msgs in
grind_pattern deprecatedThm => replacementDef n

/--
warning: `deprecatedThm` has been deprecated: Use `replacementThm` instead

Hint: Replace the deprecated name:
  d̵e̵p̵r̵e̵c̵a̵t̵e̵d̵T̵h̵m̵r̲e̲p̲l̲a̲c̲e̲m̲e̲n̲t̲T̲h̲m̲
-/
#guard_msgs in
norm_cast_add_elim deprecatedThm

-- Deprecated theorems should not be tagged with `[grind]`, but the test needs such a theorem.
set_option linter.deprecated false in
@[grind =, deprecated replacementThm (since := "2025-01-01")]
theorem deprecatedGrindThm (n : Nat) : replacementDef n = n + 1 := rfl

/--
warning: `deprecatedGrindThm` has been deprecated: Use `replacementThm` instead

Hint: Replace the deprecated name:
  d̵e̵p̵r̵e̵c̵a̵t̵e̵d̵G̵r̵i̵n̵d̵T̵h̵m̵r̲e̲p̲l̲a̲c̲e̲m̲e̲n̲t̲T̲h̲m̲
-/
#guard_msgs in
#grind_lint mute deprecatedGrindThm

-- Deprecated theorems should not be tagged with `[grind]`, but the test needs such a theorem.
set_option linter.deprecated false in
@[grind =, deprecated replacementThm (since := "2025-01-01")]
theorem deprecatedGrindThm2 (n : Nat) : replacementDef n = n + 1 := rfl

/--
warning: `deprecatedGrindThm2` has been deprecated: Use `replacementThm` instead

Hint: Replace the deprecated name:
  d̵e̵p̵r̵e̵c̵a̵t̵e̵d̵G̵r̵i̵n̵d̵T̵h̵m̵2̵r̲e̲p̲l̲a̲c̲e̲m̲e̲n̲t̲T̲h̲m̲
-/
#guard_msgs in
#grind_lint skip deprecatedGrindThm2
