import Lean

/-!
Tests that structure instances report deprecated fields once, with a hint to switch to the
replacement field, when the field could be omitted: because it has a default value or autoParam, or
because the instance has sources or `..`. Patterns, which only read fields, always report them.
-/

set_option linter.deprecated true

structure S where
  replacementField : Nat := 0
  deprecatedField : Nat := 0
attribute [deprecated S.replacementField (since := "2025-01-01")] S.deprecatedField

/--
warning: `S.deprecatedField` has been deprecated: Use `S.replacementField` instead

Hint: Replace the deprecated name:
  d̵e̵p̵r̵e̵c̵a̵t̵e̵d̵F̵i̵e̵l̵d̵r̲e̲p̲l̲a̲c̲e̲m̲e̲n̲t̲F̲i̲e̲l̲d̲
-/
#guard_msgs in
example : S := { deprecatedField := 2 }

/--
warning: `S.deprecatedField` has been deprecated: Use `S.replacementField` instead

Hint: Replace the deprecated name:
  d̵e̵p̵r̵e̵c̵a̵t̵e̵d̵F̵i̵e̵l̵d̵r̲e̲p̲l̲a̲c̲e̲m̲e̲n̲t̲F̲i̲e̲l̲d̲
-/
#guard_msgs in
example : S := { replacementField := 1, deprecatedField := 2 }

/--
warning: `S.deprecatedField` has been deprecated: Use `S.replacementField` instead

Hint: Replace the deprecated name:
  d̵e̵p̵r̵e̵c̵a̵t̵e̵d̵F̵i̵e̵l̵d̵r̲e̲p̲l̲a̲c̲e̲m̲e̲n̲t̲F̲i̲e̲l̲d̲
-/
#guard_msgs in
example (s : S) : S := { s with deprecatedField := 2 }

/--
warning: `S.deprecatedField` has been deprecated: Use `S.replacementField` instead

Hint: Replace the deprecated name:
  d̵e̵p̵r̵e̵c̵a̵t̵e̵d̵F̵i̵e̵l̵d̵r̲e̲p̲l̲a̲c̲e̲m̲e̲n̲t̲F̲i̲e̲l̲d̲
-/
#guard_msgs in
example (deprecatedField : Nat) : S := { deprecatedField }

/--
warning: `S.deprecatedField` has been deprecated: Use `S.replacementField` instead

Hint: Replace the deprecated name:
  d̵e̵p̵r̵e̵c̵a̵t̵e̵d̵F̵i̵e̵l̵d̵r̲e̲p̲l̲a̲c̲e̲m̲e̲n̲t̲F̲i̲e̲l̲d̲
-/
#guard_msgs in
example (s : S) : Nat := match s with | { deprecatedField := x, .. } => x

structure T extends S where
  y : Nat := 0

/--
warning: `S.deprecatedField` has been deprecated: Use `S.replacementField` instead

Hint: Replace the deprecated name:
  d̵e̵p̵r̵e̵c̵a̵t̵e̵d̵F̵i̵e̵l̵d̵r̲e̲p̲l̲a̲c̲e̲m̲e̲n̲t̲F̲i̲e̲l̲d̲
-/
#guard_msgs in
example : T := { deprecatedField := 2 }

#guard_msgs in
example : S := { replacementField := 1 }

/-! Fields without a default value cannot be omitted, so setting them is only reported if they could be. -/

structure R where
  replacementField : Nat := 0
  deprecatedField : Nat
attribute [deprecated R.replacementField (since := "2025-01-01")] R.deprecatedField

#guard_msgs in
example : R := { replacementField := 1, deprecatedField := 2 }

#guard_msgs in
example : R := { deprecatedField := 2 }

/--
warning: `R.deprecatedField` has been deprecated: Use `R.replacementField` instead

Hint: Replace the deprecated name:
  d̵e̵p̵r̵e̵c̵a̵t̵e̵d̵F̵i̵e̵l̵d̵r̲e̲p̲l̲a̲c̲e̲m̲e̲n̲t̲F̲i̲e̲l̲d̲
-/
#guard_msgs in
example (r : R) : R := { r with deprecatedField := 2 }

/--
warning: `R.deprecatedField` has been deprecated: Use `R.replacementField` instead

Hint: Replace the deprecated name:
  d̵e̵p̵r̵e̵c̵a̵t̵e̵d̵F̵i̵e̵l̵d̵r̲e̲p̲l̲a̲c̲e̲m̲e̲n̲t̲F̲i̲e̲l̲d̲
-/
#guard_msgs in
example : R := { deprecatedField := 2, .. }

/--
warning: `R.deprecatedField` has been deprecated: Use `R.replacementField` instead

Hint: Replace the deprecated name:
  d̵e̵p̵r̵e̵c̵a̵t̵e̵d̵F̵i̵e̵l̵d̵r̲e̲p̲l̲a̲c̲e̲m̲e̲n̲t̲F̲i̲e̲l̲d̲
-/
#guard_msgs in
example (r : R) : Nat := match r with | { deprecatedField := x, .. } => x

-- A default value added by an extending structure makes the field optional there.
structure R' extends R where
  deprecatedField := 0

/--
warning: `R.deprecatedField` has been deprecated: Use `R.replacementField` instead

Hint: Replace the deprecated name:
  d̵e̵p̵r̵e̵c̵a̵t̵e̵d̵F̵i̵e̵l̵d̵r̲e̲p̲l̲a̲c̲e̲m̲e̲n̲t̲F̲i̲e̲l̲d̲
-/
#guard_msgs in
example : R' := { deprecatedField := 2 }

-- An autoParam makes the field optional.
structure A where
  replacementField : Nat := 0
  deprecatedField : Nat := by exact 0
attribute [deprecated A.replacementField (since := "2025-01-01")] A.deprecatedField

/--
warning: `A.deprecatedField` has been deprecated: Use `A.replacementField` instead

Hint: Replace the deprecated name:
  d̵e̵p̵r̵e̵c̵a̵t̵e̵d̵F̵i̵e̵l̵d̵r̲e̲p̲l̲a̲c̲e̲m̲e̲n̲t̲F̲i̲e̲l̲d̲
-/
#guard_msgs in
example : A := { deprecatedField := 2 }

/-! Configuration structures given with `(config := { ... })` -/

open Lean

structure Cfg where
  replacementField : Bool := false
  deprecatedField : Bool := false
  deriving Repr
attribute [deprecated Cfg.replacementField (since := "2025-01-01")] Cfg.deprecatedField

-- The generated code sets every field, but is not reported.
#guard_msgs in
declare_config_elab elabCfg Cfg

elab "cfg_tac" cfg:Parser.Tactic.optConfig : tactic => do
  discard <| elabCfg cfg

/--
warning: `Cfg.deprecatedField` has been deprecated: Use `Cfg.replacementField` instead

Hint: Replace the deprecated name:
  d̵e̵p̵r̵e̵c̵a̵t̵e̵d̵F̵i̵e̵l̵d̵r̲e̲p̲l̲a̲c̲e̲m̲e̲n̲t̲F̲i̲e̲l̲d̲
-/
#guard_msgs in
example : True := by cfg_tac (config := { deprecatedField := true }); trivial
