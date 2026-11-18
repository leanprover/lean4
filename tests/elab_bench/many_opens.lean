import Lean

/-!
Benchmark for name resolution in a file with many `open` namespaces.
Every global identifier is looked up in each opened namespace, and each failed candidate runs the
reserved name predicates. The Lean code generated from Sail (e.g. the RISC-V model) opens about
200 namespaces in each file.
-/

open Lean Elab Command

elab "#many_opens" : command => do
  let bench := (← IO.getEnv "TEST_BENCH") == some "1"
  let numNs := 200
  let numDefs := if bench then 200 else 50
  for i in [:numNs] do
    let ns := mkIdent (Name.mkSimple s!"Ns{i}")
    elabCommand (← `(namespace $ns def dummy : Nat := 0 end $ns))
  for i in [:numNs] do
    let ns := mkIdent (Name.mkSimple s!"Ns{i}")
    elabCommand (← `(open $ns:ident))
  let c := mkIdent `c
  elabCommand (← `(def $c : Nat := 0))
  let cs := Array.replicate 50 c
  -- Without info trees, so that the linters do not traverse the info trees of all definitions.
  withEnableInfoTree false do
  for i in [:numDefs] do
    let d := mkIdent (Name.mkSimple s!"d{i}")
    elabCommand (← `(noncomputable def $d : Array Nat := #[$cs,*]))

#many_opens
