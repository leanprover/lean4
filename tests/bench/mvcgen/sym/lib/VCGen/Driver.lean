/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module
public import Lean.Elab
public import Lean.Meta
public meta import Lean.Elab
public meta import Lean.Meta
public meta import Lean.Meta.Tactic.Grind.Main
public meta import Lean.Meta.Tactic.Grind.Solve
public meta import VCGen.Context
public meta import VCGen.Util
public meta import VCGen.Solve

open Lean Meta Elab Tactic Sym
open Lean.Elab.Tactic.Do.SpecAttr
open Std.Do

/-!
Worklist driver for `mvcgen'`. Wraps `solve` with a queue of pending goals,
emits VCs (or invariant holes) for those `solve` cannot decompose further,
and runs the user-configured `preTac` on each emitted VC.
-/

namespace VCGen

/--
Runs the `preTac` on the VC:
- `.grind`: tries to solve the VC using the accumulated `Grind.Goal` state via `Grind.Goal.grind`.
- `.tactic`: runs the user-provided tactic on the VC, potentially emitting multiple subgoals.
- `.none`: returns the VC as-is.
-/
public meta def PreTac.run : PreTac →  Grind.Goal → VCGenM (List MVarId)
  | .none, goal => return [goal.mvarId]
  | .grind, goal => do
    let savedMCtx ← getMCtx
    match ← goal.grind with
    | .closed => return []
    | .failed .. =>
      setMCtx savedMCtx
      return [goal.mvarId]
  | .tactic tac, goal =>
    try
      let (gs, _) ← Lean.Elab.runTactic goal.mvarId tac {} {}
      pure gs
    catch _ =>
      pure [goal.mvarId]

/--
Called when decomposing the goal further did not succeed; in this case we emit a VC for the goal.
-/
public meta def emitVC (goal : Grind.Goal) : VCGenM Unit := do
  let ty ← goal.mvarId.getType
  if isSpecInvariantType (← getEnv) ty then
    goal.mvarId.setKind .syntheticOpaque
    modify fun s => { s with invariants := s.invariants.push goal.mvarId }
    return
  let goal ← (← read).preTac.processHypotheses goal
  let mut vcs := #[]
  let some mvarId ← repeatAndRfl goal.mvarId | return
  let goal := { goal with mvarId := mvarId }
  for mvarId in (← (← read).preTac.run goal) do
    mvarId.setKind .syntheticOpaque
    vcs := vcs.push mvarId
  modify fun s => { s with vcs := s.vcs ++ vcs }

public meta def work (goal : Grind.Goal) : VCGenM Unit := do
  let mvarId ← preprocessMVar goal.mvarId
  let goal := { goal with mvarId }
  let mut worklist := #[goal]
  repeat do
    let mut some goal := worklist.back? | break
    worklist := worklist.pop
    let res ← solve goal.mvarId
    match res with
    | .noEntailment .. | .noProgramFoundInTarget .. =>
      emitVC goal
    | .noSpecFoundForProgram prog _ #[] =>
      throwError "No spec found for program {prog}."
    | .noSpecFoundForProgram prog monad thms =>
      throwError "No spec matching the monad {monad} found for program {prog}. Candidates were {thms.map (·.proof)}."
    | .noStrategyForProgram prog =>
      throwError "Did not know how to decompose weakest precondition for {prog}"
    | .goals subgoals =>
      -- In grind mode with multiple subgoals, preprocess pending hypotheses
      -- to share E-graph context before forking.
      if subgoals.length > 1 then
        goal ← (← read).preTac.processHypotheses goal
      worklist := worklist ++ (subgoals |>.map ({ goal with mvarId := · }) |>.reverse)

public structure Result where
  invariants : Array MVarId
  vcs : Array MVarId

/--
Generate verification conditions for a goal of the form `P ⊢ₛ wp⟦e⟧ Q s₁ ... sₙ` by repeatedly
decomposing `e` using registered `@[spec]` theorems.
Return the VCs and invariant goals.
When `grindMode` is true, integrates grind into the VCGen loop for incremental context
internalization, avoiding O(n) re-internalization per VC.
-/
public meta partial def main (goal : MVarId) (ctx : Context) : Grind.GrindM Result := do
  let grindGoal ← Grind.mkGoalCore goal
  let ((), state) ← StateRefT'.run (ReaderT.run (work grindGoal) ctx) {}
  _ ← state.invariants.mapIdxM fun idx mv => do
    mv.setTag (Name.mkSimple ("inv" ++ toString (idx + 1)))
  _ ← state.vcs.mapIdxM fun idx mv => do
    mv.setTag (Name.mkSimple ("vc" ++ toString (idx + 1)) ++ (← mv.getTag).eraseMacroScopes)
  let invariants ← state.invariants.filterM (not <$> ·.isAssigned)
  let vcs ← state.vcs.filterM (not <$> ·.isAssigned)
  return { invariants, vcs }

end VCGen
