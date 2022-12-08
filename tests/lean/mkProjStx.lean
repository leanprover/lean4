import Lean

structure A where
  x : Nat := 0

structure B extends A where
  y : Nat := 0

structure C extends B where
  z : Nat := 0

def c : C := {}

open Lean
open Lean.Elab

def tst (varName structName fieldName : Name) : TermElabM Unit := do
  let c := mkIdent varName
  let some p ← Lean.Elab.Term.StructInst.mkProjStx? c structName fieldName | throwError "failed"
  let p ← Term.elabTerm p none
  logInfo s!"{p}"

#eval tst `c `C `x
#eval tst `c `C `y
#eval tst `c `C `z
