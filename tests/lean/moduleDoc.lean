import Lean

/-! Testing module documentation. -/

open Lean

def tst : MetaM Unit := do
  let docs := getMainModuleDoc (← getEnv)
  IO.println <| docs.toList.map repr

/-! Another module doc. -/

#eval tst
