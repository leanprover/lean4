import Lean.Elab.ConfigEval
import Lean.Elab.Deriving.FromToJson
import Lean.Elab.Tactic.Basic

/-!
Generated configuration setters and JSON decoders must not warn about deprecated
fields merely because they construct a structure instance.
-/

open Lean Elab

set_option linter.deprecated true

structure MyConfig where
  newOpt : Bool := false
  oldOpt : Bool := false
  oldCount : Nat := 0
  deriving BEq

attribute [deprecated MyConfig.newOpt (since := "2026-01-01")] MyConfig.oldOpt
attribute [deprecated "Use another option" (since := "2026-01-01")] MyConfig.oldCount

-- Cover the generated setters for both boolean and non-boolean options.
#guard_msgs in
declare_config_elab elabMyConfig MyConfig

#guard_msgs in
deriving instance FromJson for MyConfig

-- Deprecated fields are still decoded.
#guard (fromJson? (α := MyConfig)
  (Json.mkObj [("newOpt", toJson false), ("oldOpt", toJson true), ("oldCount", toJson 7)])).toOption ==
  some (MyConfig.mk false true 7)

elab "eval_my_config" cfg:optConfig : tactic => do
  discard <| elabMyConfig cfg

@[deprecated "Use true" (since := "2026-01-01")]
def oldBool : Bool := true

-- Suppressing generated setters must not suppress deprecations in user expressions.
/-- warning: `oldBool` has been deprecated: Use true -/
#guard_msgs in
example : True := by
  eval_my_config (newOpt := oldBool)
  trivial

-- Explicit assignments still warn after generating the elaborator and decoder.
/-- warning: `MyConfig.oldOpt` has been deprecated: Use `MyConfig.newOpt` instead -/
#guard_msgs in
example : MyConfig := { oldOpt := true }
