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
import Init.While
import Std.Data.HashSet

namespace Lake.Check

namespace Compare

structure Context where
  challenge : LeanExport.ExportedEnv
  solution : LeanExport.ExportedEnv
  definitionTargets : Std.HashSet Lean.Name
  theoremTargets : Std.HashSet Lean.Name

structure State where
  worklist : Array Lean.Name
  checked : Std.HashSet Lean.Name

abbrev CompareM := ReaderT Context <| StateT State <| Except String

def addWorklist (n : Lean.Name) : CompareM Unit := do
  if !(← get).checked.contains n then
    modify fun s => { s with worklist := s.worklist.push n }

def addRelevantConsts (info : Lean.ConstantInfo) : CompareM Unit := do
  runForUsedConsts info addWorklist

partial def loop : CompareM Unit := do
  if (← get).worklist.isEmpty then
    return ()

  let target ← modifyGet fun s => (s.worklist.back!, { s with worklist := s.worklist.pop })
  if (← get).checked.contains target then
    loop
  else
    let some challengeConst := (← read).challenge.constMap[target]?
      | throw s!"Const not found in challenge '{target}'"
    let some solutionConst := (← read).solution.constMap[target]?
      | throw s!"Const not found in solution '{target}'"

    if (← read).definitionTargets.contains solutionConst.name
        || (← read).theoremTargets.contains solutionConst.name then
      solutionConst.type.getUsedConstants.forM addWorklist
    else
      if challengeConst != solutionConst then
        throw s!"Const does not match between challenge and target '{target}'"
      addRelevantConsts solutionConst

    modify fun s => { s with checked := s.checked.insert target }
    loop

end Compare

public def definitionHoleMatches (challengeHole solutionHole : Lean.DefinitionVal) : Bool :=
  challengeHole.toConstantVal == solutionHole.toConstantVal
    && challengeHole.safety == solutionHole.safety

public def compareAt (challenge solution : LeanExport.ExportedEnv) (theoremTargets : Array Lean.Name)
    (definitionTargets : Array Lean.Name) (primitive : Array Lean.Name) : Except String Unit := do
  let mut worklist := primitive

  for target in theoremTargets do
    let some challengeConst := challenge.constMap[target]?
      | throw s!"Const not found in challenge: '{target}'"

    let some solutionConst := solution.constMap[target]?
      | throw s!"Const not found in solution: '{target}'"

    let (challengeConst, solutionConst) ←
      match challengeConst, solutionConst with
      | .thmInfo cc, .thmInfo sc
      | .axiomInfo cc, .axiomInfo sc => pure (cc.toConstantVal, sc.toConstantVal)
      | _, _ => throw s!"Challenge and solution constant kind don't match: '{target}'"

    if challengeConst != solutionConst then
      throw s!"Challenge and solution theorem statement do not match: '{target}'"

    worklist := worklist ++ challengeConst.type.getUsedConstants

  for target in definitionTargets do
    let some challengeConst := challenge.constMap[target]?
      | throw s!"Const not found in challenge: '{target}'"

    let some solutionConst := solution.constMap[target]?
      | throw s!"Const not found in solution: '{target}'"

    let .defnInfo challengeConst := challengeConst
      | throw s!"Challenge constant is not a definition: '{target}'"
    let .defnInfo solutionConst := solutionConst
      | throw s!"Solution constant is not a definition: '{target}'"

    unless challengeConst.value.getLambdaBody.isAppOf ``sorryAx do
      throw s!"Challenge definition is not sorried: '{target}'"

    if !definitionHoleMatches challengeConst solutionConst then
      throw s!"Const does not match between challenge and target '{target}'"

    worklist := worklist.push solutionConst.name

  let definitionTargets := Std.HashSet.ofArray definitionTargets
  let theoremTargets := Std.HashSet.ofArray theoremTargets
  Compare.loop.run { challenge, solution, definitionTargets, theoremTargets } |>.run' { worklist, checked := {} }

/-- Match an exact approved proposition, or a conjunction of such propositions. -/
partial def matchAcceptedInput (accepted : Array (Prod Lean.Name Lean.Expr))
    (input : Lean.Expr) : Option (Array Lean.Name) := do
  for (name, statement) in accepted do
    if input == .const name [] || input == statement then
      return #[name]
  if input.isAppOfArity ``And 2 then
    let left <- matchAcceptedInput accepted input.appFn!.appArg!
    let right <- matchAcceptedInput accepted input.appArg!
    return left ++ right
  none

/--
Compare with additional, closed proposition hypotheses explicitly approved by the challenge author.
Only leading, nondependent hypotheses may be removed. The returned names are the hypotheses of
each conditional theorem, in occurrence order without duplicates, not an audit of proof-term usage.
The original solution must still be checked for axioms and replayed through the kernel.
-/
public def compareWithAcceptedStatements (challenge solution : LeanExport.ExportedEnv)
    (theoremTargets definitionTargets primitive acceptedNames : Array Lean.Name) :
    Except String (Array (Prod Lean.Name (Array Lean.Name))) := do
  if acceptedNames.isEmpty then
    compareAt challenge solution theoremTargets definitionTargets primitive
    return #[]

  let mut accepted := #[]
  for name in acceptedNames do
    if theoremTargets.contains name || definitionTargets.contains name then
      throw s!"Accepted statement cannot be a comparison target: '{name}'"
    let some (.defnInfo info) := challenge.constMap[name]?
      | throw s!"Accepted statement must be a closed proposition definition: '{name}'"
    unless info.type == .sort .zero && info.levelParams.isEmpty && info.safety == .safe do
      throw s!"Accepted statement must be a closed proposition definition: '{name}'"
    accepted := accepted.push (name, info.value)

  let mut report := #[]
  let mut inputConsts := #[]
  let mut comparisonSolution := solution
  for target in theoremTargets do
    let some (.thmInfo cc) := challenge.constMap[target]? | continue
    let some (.thmInfo sc) := solution.constMap[target]? | continue
    let mut type := sc.type
    let mut used := #[]
    while type != cc.type do
      let .forallE _ input body _ := type
        | throw s!"Unaccepted conditional input or mismatched conclusion: '{target}'"
      -- A removed proof must not change the remaining statement or later hypotheses.
      if body.hasLooseBVars then
        throw s!"Dependent conditional input is not supported: '{target}'"
      let some names := matchAcceptedInput accepted input
        | throw s!"Unaccepted conditional input or mismatched conclusion: '{target}'"
      for name in names do
        unless used.contains name do
          used := used.push name
      inputConsts := inputConsts ++ input.getUsedConstants
      type := body
    unless used.isEmpty do
      report := report.push (target, used)
      -- This copy is solely for structural comparison; no checker receives a rewritten theorem.
      comparisonSolution := { comparisonSolution with
        constMap := comparisonSolution.constMap.insert target (.thmInfo { sc with type }) }

  -- No theorem/definition-hole exemptions apply to accepted statements or their dependencies.
  -- This also checks And itself when conjunctions were stripped from a theorem's type.
  Compare.loop.run { challenge, solution, definitionTargets := {}, theoremTargets := {} }
    |>.run' { worklist := inputConsts, checked := {} }
  compareAt challenge comparisonSolution theoremTargets definitionTargets primitive
  return report

end Lake.Check
