import Lean

open Lean
open Lean.Compiler

/-- info: -/
#guard_msgs in
#eval (do assert! hasCSimpAttribute (← getEnv) ``List.map_eq_mapTR : MetaM Unit)

/-- info: -/
#guard_msgs in
#eval (do assert! hasCSimpAttribute (← getEnv) ``List.append_eq_appendTR : MetaM Unit)

/-- info: -/
#guard_msgs in
#eval (do assert! !hasCSimpAttribute (← getEnv) ``List.append : MetaM Unit)
