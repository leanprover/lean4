import Lean

open Lean
open Lean.Meta

-- Return true if `declName` should be ignored
def shouldIgnore (declName : Name) : Bool :=
  declName.isInternal
  || match declName with
     | .str _ s => "match_".isPrefixOf s || "proof_".isPrefixOf s || "eq_".isPrefixOf s
     | _ => true

-- Print declarations that have the given prefix.
def printDecls (pre : Name) : MetaM Unit := do
  let cs := (← getEnv).constants
  cs.forM fun declName info => do
    if pre.isPrefixOf declName && !shouldIgnore declName then
      if let some docString ← findDocString? (← getEnv) declName then
        IO.println s!"/-- {docString} -/\n{declName} : {← ppExpr info.type}"
      else
        IO.println s!"{declName} : {← ppExpr info.type}"

#eval printDecls `Array
#eval printDecls `List
#eval printDecls `Bool
#eval printDecls `Lean.Elab
