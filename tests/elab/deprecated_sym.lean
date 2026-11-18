/-!
Tests that the tactics of `sym` mode and the `register_sym_simp` and `register_sym_dsimp` commands
report deprecated theorems, but not deprecated definitions, which they unfold.
-/

set_option linter.deprecated true

def replacementDef (n : Nat) : Nat := n + 1
@[deprecated replacementDef (since := "2025-01-01")] def deprecatedDef (n : Nat) : Nat := n + 1

theorem replacementThm (n : Nat) : replacementDef n = n + 1 := rfl
@[deprecated replacementThm (since := "2025-01-01")]
theorem deprecatedThm (n : Nat) : replacementDef n = n + 1 := rfl

/--
warning: `deprecatedThm` has been deprecated: Use `replacementThm` instead

Hint: Replace the deprecated name:
  d̵e̵p̵r̵e̵c̵a̵t̵e̵d̵T̵h̵m̵r̲e̲p̲l̲a̲c̲e̲m̲e̲n̲t̲T̲h̲m̲
-/
#guard_msgs in
example (n : Nat) : replacementDef n = n + 1 := by sym => apply deprecatedThm

/--
warning: `deprecatedThm` has been deprecated: Use `replacementThm` instead

Hint: Replace the deprecated name:
  d̵e̵p̵r̵e̵c̵a̵t̵e̵d̵T̵h̵m̵r̲e̲p̲l̲a̲c̲e̲m̲e̲n̲t̲T̲h̲m̲
-/
#guard_msgs in
example (n : Nat) : replacementDef n = n + 1 := by sym => simp [deprecatedThm]

/--
warning: `deprecatedThm` has been deprecated: Use `replacementThm` instead

Hint: Replace the deprecated name:
  d̵e̵p̵r̵e̵c̵a̵t̵e̵d̵T̵h̵m̵r̲e̲p̲l̲a̲c̲e̲m̲e̲n̲t̲T̲h̲m̲
-/
#guard_msgs in
example (x y : Nat) (h : x + 1 = y) : replacementDef x = y := by
  sym =>
    dsimp [deprecatedThm]
    exact h

#guard_msgs in
example (x y : Nat) (h : x + 1 = y) : (set_option linter.deprecated false in deprecatedDef) x = y := by
  sym =>
    dsimp [deprecatedDef]
    exact h

/--
warning: `deprecatedThm` has been deprecated: Use `replacementThm` instead

Hint: Replace the deprecated name:
  d̵e̵p̵r̵e̵c̵a̵t̵e̵d̵T̵h̵m̵r̲e̲p̲l̲a̲c̲e̲m̲e̲n̲t̲T̲h̲m̲
-/
#guard_msgs in
register_sym_simp symSimpSet where
  post := ground >> rewrite [deprecatedThm]

/--
warning: `deprecatedThm` has been deprecated: Use `replacementThm` instead

Hint: Replace the deprecated name:
  d̵e̵p̵r̵e̵c̵a̵t̵e̵d̵T̵h̵m̵r̲e̲p̲l̲a̲c̲e̲m̲e̲n̲t̲T̲h̲m̲
-/
#guard_msgs in
register_sym_dsimp symDSimpSet where
  post := ground >> rewrite [deprecatedThm]
