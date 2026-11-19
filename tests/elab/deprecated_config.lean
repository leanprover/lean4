import Lean

/-!
Tests that configuration syntax reports deprecated fields and constructors once, with a hint to
switch to the replacement, and that `declare_config_elab` does not report the code it generates.
-/

set_option linter.deprecated true

open Lean

structure Cfg where
  replacementField : Bool := false
  deprecatedField : Bool := false
  deriving Repr
attribute [deprecated Cfg.replacementField (since := "2025-01-01")] Cfg.deprecatedField

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
example : True := by cfg_tac +deprecatedField; trivial

/--
warning: `Cfg.deprecatedField` has been deprecated: Use `Cfg.replacementField` instead

Hint: Replace the deprecated name:
  d̵e̵p̵r̵e̵c̵a̵t̵e̵d̵F̵i̵e̵l̵d̵r̲e̲p̲l̲a̲c̲e̲m̲e̲n̲t̲F̲i̲e̲l̲d̲
-/
#guard_msgs in
example : True := by cfg_tac -deprecatedField; trivial

/--
warning: `Cfg.deprecatedField` has been deprecated: Use `Cfg.replacementField` instead

Hint: Replace the deprecated name:
  d̵e̵p̵r̵e̵c̵a̵t̵e̵d̵F̵i̵e̵l̵d̵r̲e̲p̲l̲a̲c̲e̲m̲e̲n̲t̲F̲i̲e̲l̲d̲
-/
#guard_msgs in
example : True := by cfg_tac (deprecatedField := true); trivial

#guard_msgs in
example : True := by cfg_tac +replacementField; trivial

inductive Mode where
  | otherCtor
  | replacementCtor
  | deprecatedCtor
  deriving Repr
attribute [deprecated Mode.replacementCtor (since := "2025-01-01")] Mode.deprecatedCtor

structure ModeCfg where
  m : Mode := .otherCtor
  deriving Repr

-- The generated code refers to all constructors, including deprecated ones.
#guard_msgs in
declare_config_elab elabModeCfg ModeCfg

elab "mode_cfg_tac" cfg:Parser.Tactic.optConfig : tactic => do
  discard <| elabModeCfg cfg

/--
warning: `Mode.deprecatedCtor` has been deprecated: Use `Mode.replacementCtor` instead

Hint: Replace the deprecated name:
  .̵d̵e̵p̵r̵e̵c̵a̵t̵e̵d̵C̵t̵o̵r̵.̲r̲e̲p̲l̲a̲c̲e̲m̲e̲n̲t̲C̲t̲o̲r̲
-/
#guard_msgs in
example : True := by mode_cfg_tac (m := .deprecatedCtor); trivial

/--
warning: `Mode.deprecatedCtor` has been deprecated: Use `Mode.replacementCtor` instead

Hint: Replace the deprecated name:
  M̵o̵d̵e̵.̵d̵e̵p̵r̵e̵c̵a̵t̵e̵d̵C̵t̵o̵r̵M̲o̲d̲e̲.̲r̲e̲p̲l̲a̲c̲e̲m̲e̲n̲t̲C̲t̲o̲r̲
-/
#guard_msgs in
example : True := by mode_cfg_tac (m := Mode.deprecatedCtor); trivial

/--
warning: `Mode.deprecatedCtor` has been deprecated: Use `Mode.replacementCtor` instead

Hint: Replace the deprecated name:
  d̵e̵p̵r̵e̵c̵a̵t̵e̵d̵C̵t̵o̵r̵r̲e̲p̲l̲a̲c̲e̲m̲e̲n̲t̲C̲t̲o̲r̲
-/
#guard_msgs in
example : True := by mode_cfg_tac (m := deprecatedCtor); trivial

#guard_msgs in
example : True := by mode_cfg_tac (m := .replacementCtor); trivial
