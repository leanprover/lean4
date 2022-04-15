import Lean

open Lean
open Lean.Compiler

#eval (do assert! hasCSimpAttribute (← getEnv) ``List.map_eq_mapTR : MetaM Unit)
#eval (do assert! hasCSimpAttribute (← getEnv) ``List.append_eq_appendTR : MetaM Unit)
#eval (do assert! !hasCSimpAttribute (← getEnv) ``List.append : MetaM Unit)
