import Lean

/-! Testing module documentation. -/

open Lean

def tst : MetaM Unit := do
  let docs := getMainModuleDoc (← getEnv)
  IO.println <| docs.toList.map repr

def printDoc (moduleName : Name) : MetaM Unit := do
  match getModuleDoc? (← getEnv) moduleName with
  | some docs => IO.println <| docs.toList.map repr
  | _ => throwError "module not found"

/-! Another module doc. -/

#eval tst

#eval printDoc `Lean.Meta.ReduceEval
#eval printDoc `Lean.Data.Lsp.Communication
