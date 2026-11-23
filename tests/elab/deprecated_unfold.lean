import Lean
import Std.Tactic.BVDecide

/-!
Tests which tactic arguments the `deprecated` linter reports, depending on what the tactic does
with the deprecated constant.

Unfolding a deprecated definition, doing induction or case analysis on its calls, or selecting a
deprecated structure for `bv_decide`'s type analysis is not reported: the tactic acts on occurrences
already in the goal, so the deprecated name cannot be replaced there, and the use that put it in the
goal is reported where it occurs.

Using a deprecated theorem in the same tactics is reported with a replacement hint, but erasing one
is not, since it can only be erased by its own name.
-/

set_option linter.deprecated true

def replacementDef (n : Nat) : Nat := n + 1
@[deprecated replacementDef (since := "2025-01-01")]
def deprecatedDef (n : Nat) : Nat := n + 1

def replacementRecDef : Nat → Nat
  | 0 => 0
  | n + 1 => replacementRecDef n
@[deprecated replacementRecDef (since := "2025-01-01")]
def deprecatedRecDef : Nat → Nat
  | 0 => 0
  | n + 1 => deprecatedRecDef n

@[grind =] theorem replacementThm (n : Nat) : replacementDef n = n + 1 := rfl
-- Deprecated theorems should not be tagged with `[grind]`, but the test needs such a theorem.
set_option linter.deprecated false in
@[grind =, deprecated replacementThm (since := "2025-01-01")]
theorem deprecatedThm (n : Nat) : replacementDef n = n + 1 := rfl

/-! Unfolding deprecated definitions is not reported. -/

#guard_msgs in
example (n : Nat) : (set_option linter.deprecated false in deprecatedDef) n = n + 1 := by
  unfold deprecatedDef; rfl

#guard_msgs in
example (n : Nat) : (set_option linter.deprecated false in deprecatedDef) n = n + 1 := by
  conv => unfold deprecatedDef

#guard_msgs in
example (n : Nat) : (set_option linter.deprecated false in deprecatedDef) n = n + 1 := by
  delta deprecatedDef; rfl

#guard_msgs in
example (n : Nat) : (set_option linter.deprecated false in deprecatedDef) n = n + 1 := by
  conv => delta deprecatedDef

#guard_msgs in
example (n : Nat) : (set_option linter.deprecated false in deprecatedDef) n = n + 1 := by
  rw [deprecatedDef]

#guard_msgs in
example (n : Nat) : (set_option linter.deprecated false in deprecatedDef) n = n + 1 := by
  simp [deprecatedDef]

#guard_msgs in
example (n : Nat) : (set_option linter.deprecated false in deprecatedDef) n = n + 1 := by
  simp only [deprecatedDef]

#guard_msgs in
example (n : Nat) : (set_option linter.deprecated false in deprecatedDef) n = n + 1 := by
  dsimp [deprecatedDef]

#guard_msgs in
example (n : Nat) : (set_option linter.deprecated false in deprecatedDef) n = n + 1 := by
  grind [deprecatedDef]

/-! Induction and case analysis on calls of deprecated functions is not reported. -/

#guard_msgs in
example (n : Nat) : (set_option linter.deprecated false in deprecatedRecDef) n = 0 := by
  fun_induction deprecatedRecDef <;> simp_all

#guard_msgs in
example (n : Nat) : (set_option linter.deprecated false in deprecatedRecDef) n = 0 := by
  fun_induction deprecatedRecDef n <;> simp_all

#guard_msgs in
example (n : Nat) :
    (set_option linter.deprecated false in deprecatedRecDef) n =
      (set_option linter.deprecated false in deprecatedRecDef) n := by
  fun_cases deprecatedRecDef <;> rfl

#guard_msgs in
example (n : Nat) :
    (set_option linter.deprecated false in deprecatedRecDef) n =
      (set_option linter.deprecated false in deprecatedRecDef) n := by
  fun_cases deprecatedRecDef n <;> rfl

/-! Selecting deprecated structures for `bv_decide`'s type analysis is not reported. -/

structure ReplacementStruct where
  x : BitVec 8
  y : BitVec 8
@[deprecated ReplacementStruct (since := "2025-01-01")] structure DeprecatedStruct where
  x : BitVec 8
  y : BitVec 8

#guard_msgs in
example (a : (set_option linter.deprecated false in DeprecatedStruct)) (h : a.x = 1) :
    a.x + 0 = 1 := by
  bv_decide types [DeprecatedStruct]

/-! Using deprecated theorems is reported with a hint. -/

/--
warning: `deprecatedThm` has been deprecated: Use `replacementThm` instead

Hint: Replace the deprecated name:
  d̵e̵p̵r̵e̵c̵a̵t̵e̵d̵T̵h̵m̵r̲e̲p̲l̲a̲c̲e̲m̲e̲n̲t̲T̲h̲m̲
-/
#guard_msgs in
example (n : Nat) : replacementDef n = n + 1 := by rw [deprecatedThm]

/--
warning: `deprecatedThm` has been deprecated: Use `replacementThm` instead

Hint: Replace the deprecated name:
  d̵e̵p̵r̵e̵c̵a̵t̵e̵d̵T̵h̵m̵r̲e̲p̲l̲a̲c̲e̲m̲e̲n̲t̲T̲h̲m̲
-/
#guard_msgs in
example (n : Nat) : replacementDef n = n + 1 := by simp only [deprecatedThm]

/--
warning: `deprecatedThm` has been deprecated: Use `replacementThm` instead

Hint: Replace the deprecated name:
  d̵e̵p̵r̵e̵c̵a̵t̵e̵d̵T̵h̵m̵r̲e̲p̲l̲a̲c̲e̲m̲e̲n̲t̲T̲h̲m̲
-/
#guard_msgs in
example (n : Nat) : replacementDef n = n + 1 := by grind only [deprecatedThm]

/-!
Erasing deprecated theorems is not reported: a theorem in the `simp` or `grind` set can only be
erased by its own name.
-/

-- Deprecated theorems should not be tagged with `[simp]`, but the test needs such a theorem.
set_option linter.deprecated false in
@[simp, deprecated replacementThm (since := "2025-01-01")]
theorem deprecatedSimpThm (n : Nat) : replacementDef n = n + 1 := rfl

#guard_msgs in
example (n : Nat) : replacementDef n = n + 1 := by grind [-deprecatedThm]

#guard_msgs in
example (n : Nat) : replacementDef n = n + 1 := by simp [replacementDef, -deprecatedSimpThm]

#guard_msgs in
example (n : Nat) : replacementDef n = n + 1 := by simp_all [replacementDef, -deprecatedSimpThm]

#guard_msgs in
example (n : Nat) : replacementDef n = n + 1 := by dsimp [replacementDef, -deprecatedSimpThm]

/-! Deprecated simprocs are reported, since they are used rather than unfolded. -/

open Lean Meta in
simproc [simp] replacementSimproc (replacementDef _) := fun _ => return .continue
open Lean Meta in
simproc deprecatedSimproc (replacementDef _) := fun _ => return .continue
attribute [deprecated replacementSimproc (since := "2025-01-01")] deprecatedSimproc

/--
warning: `deprecatedSimproc` has been deprecated: Use `replacementSimproc` instead

Hint: Replace the deprecated name:
  d̵e̵p̵r̵e̵c̵a̵t̵e̵d̵S̵i̵m̵p̵r̵o̵c̵r̲e̲p̲l̲a̲c̲e̲m̲e̲n̲t̲S̲i̲m̲p̲r̲o̲c̲
-/
#guard_msgs in
set_option linter.unusedSimpArgs false in
example (n : Nat) : replacementDef n = n + 1 := by simp [replacementDef, deprecatedSimproc]
