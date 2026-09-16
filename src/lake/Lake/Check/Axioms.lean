/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import LeanExport.Parse
import Lake.Check.Util
import Init.Data.ToString.Macro
import Std.Data.HashSet

namespace Lake.Check

namespace Axioms

structure Context where
  solution : LeanExport.ExportedEnv
  legalAxioms : Std.HashSet Lean.Name

structure State where
  worklist : Array Lean.Name
  checked : Std.HashSet Lean.Name

abbrev AxiomsM := ReaderT Context <| StateT State <| Except String

partial def loop : AxiomsM Unit := do
  if (← get).worklist.isEmpty then
    return ()

  let target ← modifyGet fun s => (s.worklist.back!, { s with worklist := s.worklist.pop })
  if (← get).checked.contains target then
    loop
  else
    let some info := (← read).solution.constMap[target]?
      | throw s!"Constant not found in solution '{target}'"

    runForUsedConsts info validateConst

    modify fun s => { s with checked := s.checked.insert target }
    loop
where
  validateConst (n : Lean.Name) : AxiomsM Unit := do
    let some info := (← read).solution.constMap[n]?
      | throw s!"Constant not found in solution '{n}'"

    if let .axiomInfo info := info then
      if !(← read).legalAxioms.contains info.name then
        throw s!"Illegal axiom detected: '{n}'"

    if !(← get).checked.contains n then
      modify fun s => { s with worklist := s.worklist.push n }

end Axioms

/--
The axioms some other constant in `env` refers to, each paired with one constant that refers to it.
-/
public def usedAxioms (env : LeanExport.ExportedEnv) : Array (Lean.Name × Lean.Name) :=
  -- `constOrder` is the export order, so the result is deterministic without needing an `Ord`.
  let collect : StateM (Std.HashSet Lean.Name × Array (Lean.Name × Lean.Name)) Unit := do
    for name in env.constOrder do
      let some info := env.constMap[name]? | continue
      runForUsedConsts info fun ref => do
        -- `runForUsedConsts` reports the constant itself, which is not an incoming reference
        unless ref == name do
          if let some (.axiomInfo ..) := env.constMap[ref]? then
            modify fun (seen, used) =>
              if seen.contains ref then (seen, used) else (seen.insert ref, used.push (ref, name))
  (collect.run ({}, #[])).2.2

public def checkAxioms (solution : LeanExport.ExportedEnv) (theoremTargets : Array Lean.Name)
    (definitionTargets : Array Lean.Name) (legalAxioms : Array Lean.Name) : Except String Unit := do
  let mut worklist := #[]
  for target in theoremTargets do
    let some solutionConst := solution.constMap[target]?
      | throw s!"Const not found in solution: '{target}'"
    let .thmInfo solutionConst := solutionConst
      | throw s!"Solution constant is not a theorem: '{target}'"
    worklist := worklist.push solutionConst.name

  for target in definitionTargets do
    let some solutionConst := solution.constMap[target]?
      | throw s!"Const not found in solution: '{target}'"
    let .defnInfo solutionConst := solutionConst
      | throw s!"Solution constant is not a definition: '{target}'"
    worklist := worklist.push solutionConst.name

  let legalAxioms := Std.HashSet.ofArray legalAxioms
  Axioms.loop.run { solution, legalAxioms } |>.run' { worklist, checked := {} }

end Lake.Check
