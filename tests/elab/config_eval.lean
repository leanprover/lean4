import Lean.Elab.ConfigEval

/-!
# Tests of `ConfigEval` configuration evaluation system
-/

open Lean Elab

/-!
Set up some configuration objects, and then derive some configuration elaborators for each monad.
We're testing inductive variants, parent structures, and embedded structures.
-/

inductive TransparencyMode where
  | default
  | all
  | none
  deriving ToExpr

structure ParentCfg1 where
  parentBoolVal : Bool := false
  deriving ToExpr

structure SubCfg1 where
  bool : Bool := false
  nat : Nat := 0
  transparency : TransparencyMode := .default
  deriving ToExpr

structure Cfg1 extends ParentCfg1 where
  boolVal : Bool := false
  natVal : Nat := 0
  intVal : Int := 0
  strVal : String := ""
  extra : SubCfg1 := {}
  parentBoolVal := true
  deriving ToExpr

declare_core_config_elab elabCoreCfg1 Cfg1
declare_term_config_elab elabTermCfg1 Cfg1
declare_config_elab elabTacticCfg1 Cfg1
declare_command_config_elab elabCommandCfg1 Cfg1

/-!
Check the types of each of these elaborators.
-/
/--
info: elabCoreCfg1 (cfg : Syntax) (init : Cfg1 := { }) (logExceptions : Bool := false) : CoreM Cfg1
-/
#guard_msgs in #check elabCoreCfg1
/--
info: elabTermCfg1 (cfg : Syntax) (init : Cfg1 := { }) (logExceptions : Bool := true) : TermElabM Cfg1
-/
#guard_msgs in #check elabTermCfg1
/--
info: elabTacticCfg1 (cfg : Syntax) (init : Cfg1 := { }) (logExceptions : Bool := true) : Tactic.TacticM Cfg1
-/
#guard_msgs in #check elabTacticCfg1
/--
info: elabCommandCfg1 (cfg : Syntax) (init : Cfg1 := { }) (logExceptions : Bool := true) : Command.CommandElabM Cfg1
-/
#guard_msgs in #check elabCommandCfg1

/-!
Create commands and tactics to test these elaborators.
-/
elab "#test_core_cfg1" cfg:optConfig : command => Command.liftTermElabM do
  let c ← elabCoreCfg1 cfg
  logInfo m!"{toExpr c}"

elab "#test_term_cfg1" cfg:optConfig : command => Command.liftTermElabM do
  let c ← elabTermCfg1 cfg
  logInfo m!"{toExpr c}"

elab "test_tactic_cfg1" cfg:optConfig : tactic => Tactic.withMainContext do
  let c ← elabTacticCfg1 cfg
  logInfo m!"{toExpr c}"

elab "#test_command_cfg1" cfg:optConfig : command => do
  let c ← elabCommandCfg1 cfg
  logInfo m!"{toExpr c}"

/-!
Testing configuration option evaluation. Only need to exercise all the optinos for one of them.
-/
/-- info: { } -/
#guard_msgs in #test_core_cfg1
/-- info: { boolVal := true } -/
#guard_msgs in #test_core_cfg1 (boolVal := true)
/-- info: { boolVal := true } -/
#guard_msgs in #test_core_cfg1 +boolVal
/-- info: { boolVal := true, intVal := -2 } -/
#guard_msgs in #test_core_cfg1 +boolVal (intVal := -2)
/-- info: { boolVal := true, natVal := 3, intVal := -2 } -/
#guard_msgs in #test_core_cfg1 +boolVal (intVal := -2) (natVal := 3)
/-- info: { strVal := "yo" } -/
#guard_msgs in #test_core_cfg1 (strVal := "yo")
/-- info: { extra := { bool := true, nat := 3 } } -/
#guard_msgs in #test_core_cfg1 (extra := { bool := true, nat := 3 })
/-- info: { extra := { bool := true, nat := 3 } } -/
#guard_msgs in #test_core_cfg1 (extra.bool := true) (extra.nat := 3)
/-- info: { parentBoolVal := false } -/
#guard_msgs in #test_core_cfg1 -parentBoolVal
/-- info: { natVal := 4 } -/
#guard_msgs in #test_core_cfg1 (natVal := 2 + 2)
/-- info: { natVal := 100000 } -/
#guard_msgs in #test_core_cfg1 (natVal := Meta.Simp.defaultMaxSteps)
/-- info: { extra := { bool := true } } -/
#guard_msgs in #test_core_cfg1 +extra.bool
/-- info: { extra := { transparency := TransparencyMode.all } } -/
#guard_msgs in #test_core_cfg1 (extra.transparency := .all)
/-- info: { extra := { bool := true } } -/
#guard_msgs in #test_core_cfg1 (config := { extra.bool := true })

/-!
Testing that each elaborator works.
-/
/-- info: { boolVal := true } -/
#guard_msgs in #test_core_cfg1 +boolVal
/-- info: { boolVal := true } -/
#guard_msgs in #test_term_cfg1 +boolVal
/-- info: { boolVal := true } -/
#guard_msgs in example : True := by test_tactic_cfg1 +boolVal; trivial
/-- info: { boolVal := true } -/
#guard_msgs in #test_command_cfg1 +boolVal

/-!
Testing default error behaviors.
- `CoreM` doesn't allow errors
- `TermM` allows errors if errToSorry is enabled
- `TacticM` allows errors if recovery is enabled
- `CommandM` allows errors
-/

/-- error: Unknown identifier `config_eval_test.invalid` -/
#guard_msgs in #test_core_cfg1 (boolVal := config_eval_test.invalid) (natVal := 2 + 2)
/--
error: Unknown identifier `config_eval_test.invalid`
---
info: { natVal := 2 }
-/
#guard_msgs in #test_term_cfg1 (boolVal := config_eval_test.invalid) (natVal := 2)
/--
error: Type mismatch
  Nat.zero
has type
  Nat
but is expected to have type
  Bool
---
info: { natVal := 2 }
-/
#guard_msgs in #test_term_cfg1 (boolVal := Nat.zero) (natVal := 2)
/--
error: Unknown identifier `config_eval_test.invalid`
---
info: { natVal := 2 }
-/
#guard_msgs in example : True := by
  test_tactic_cfg1 (boolVal := config_eval_test.invalid) (natVal := 2)
  trivial
-- Recovery disabled -> fails, allowing `trivial` to be applied.
#guard_msgs in example : True := by
  first | test_tactic_cfg1 (boolVal := config_eval_test.invalid) (natVal := 2) | trivial
/--
error: Unknown identifier `config_eval_test.invalid`
---
info: { natVal := 4 }
-/
#guard_msgs in #test_command_cfg1 (boolVal := config_eval_test.invalid) (natVal := 2 + 2)
