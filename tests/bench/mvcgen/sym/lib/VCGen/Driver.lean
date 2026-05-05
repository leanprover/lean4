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
Try to elaborate the user's invariant alt for invariant number `n` inline,
discharging `mv` if successful. Looks up `Context.invariantAlts[n]?` (pre-parsed
in `Frontend`) and dispatches to `exact $rhs` for bullet form or
`rename_i $args*; exact $rhs` for labelled form. Returns whether elaboration
succeeded. Numbering is 1-based; out-of-order labelled forms (e.g. `| inv2 => …`
before `| inv1 => …`) are supported because the map is keyed by parsed number,
not position.
-/
private meta def tryInlineInvariant (n : Nat) (mv : MVarId) : VCGenM Bool := do
  let some alt := (← read).invariantAlts[n]? | return false
  try
    let tac ← match alt with
      | `(Lean.Parser.Tactic.invariantDotAlt| · $rhs) => `(tactic| exact $rhs)
      | `(Lean.Parser.Tactic.invariantCaseAlt| | $_tag $args* => $rhs) =>
          `(tactic| (rename_i $args*; exact $rhs))
      | _ => return false
    let _ ← Lean.Elab.runTactic mv tac {} {}
    -- The tactic runs without throwing even when it fails to close the goal;
    -- check explicitly that the MVar got assigned.
    mv.isAssigned
  catch _ =>
    return false

/-- Pull invariant subgoals out of `subgoals` and handle them eagerly: register
each in `State.invariants` (1-based stable index) and try to inline-elaborate
its matching user alt. Returns the remaining non-invariant subgoals for `work`
to enqueue. Eager handling here ensures dependent VCs see `?inv` assigned by
the time they reach `emitVC`/`preTac`. -/
private meta def handleInvariantSubgoals (subgoals : List MVarId) : VCGenM (Array MVarId) := do
  let env ← getEnv
  let mut others : Array MVarId := #[]
  for sg in subgoals do
    if isSpecInvariantType env (← sg.getType) then
      let n := (← get).invariants.size + 1
      modify fun s => { s with invariants := s.invariants.push sg }
      if ← tryInlineInvariant n sg then
        modify fun s => { s with inlineHandledInvariants := s.inlineHandledInvariants.insert n }
      else
        sg.setKind .syntheticOpaque
    else
      others := others.push sg
  return others

/--
Called when decomposing the goal further did not succeed; in this case we emit a VC for the goal.
Invariant subgoals are handled separately by `handleInvariantSubgoals` directly inside `work`,
so they never reach this path.
-/
public meta def emitVC (goal : Grind.Goal) : VCGenM Unit := do
  let goal ← (← read).preTac.processHypotheses goal
  let mut vcs := #[]
  -- `trivial`: when false, skip `repeatAndRfl` (which collapses And-chains via rfl);
  -- emit the goal as-is.
  let mvarId ←
    if (← read).trivial then
      let some mvarId ← repeatAndRfl goal.mvarId | return
      pure mvarId
    else
      pure goal.mvarId
  let goal := { goal with mvarId := mvarId }
  for mvarId in (← (← read).preTac.run goal) do
    mvarId.setKind .syntheticOpaque
    vcs := vcs.push mvarId
  modify fun s => { s with vcs := s.vcs ++ vcs }

public meta def work (goal : Grind.Goal) : VCGenM Unit := do
  let mvarId ← preprocessMVar goal.mvarId
  let goal := { goal with mvarId }
  let mut worklist := #[goal] -- worklist is LIFO (popped from the back)
  while let some goal := worklist.back? do
    worklist := worklist.pop
    if ← outOfFuel then
      emitVC goal
      continue
    let res ← solve goal.mvarId
    match res with
    | .noEntailment .. | .noProgramFoundInTarget .. =>
      emitVC goal
    | .noSpecFoundForProgram prog monad thms =>
      if (← read).errorOnMissingSpec then goal.mvarId.withContext do
        if thms.isEmpty then
          throwError "No spec found for program {prog}."
        else
          throwError "No spec matching the monad {monad} found for program {prog}. Candidates were {thms.map (·.proof)}."
      else
        emitVC goal
    | .noStrategyForProgram prog => goal.mvarId.withContext do
      throwError "Did not know how to decompose weakest precondition for {prog}"
    | .goals subgoals =>
      -- Handle invariant subgoals eagerly here, so that VC subgoals popped
      -- from the worklist later see the invariant MVar already assigned.
      -- Non-invariant subgoals go to the worklist as usual and will eventually go through `emitVC`.
      let subgoals ← handleInvariantSubgoals subgoals
      -- In grind mode with multiple subgoals, preprocess pending hypotheses
      -- to share E-graph context before forking.
      let goal ←
        if subgoals.size > 1 then
          (← read).preTac.processHypotheses goal
        else
          pure goal
      worklist := worklist ++ subgoals.reverse.map (fun sg => { goal with mvarId := sg })

public structure Result where
  /-- All invariant goals emitted during VC generation, in emit order. The MVarId at
  index `i` carries tag `inv{i+1}`, so callers can treat the array index as the
  invariant number. Some entries may already be assigned (inline-elaborated by
  `Driver.emitVC`); the caller is responsible for filtering before discharging. -/
  invariants : Array MVarId
  /-- Unassigned VCs. -/
  vcs : Array MVarId
  /-- Invariant numbers handled inline by `Driver.emitVC`. Used by `Frontend` to
  avoid spurious "alt does not match any invariant" warnings for inline-consumed
  alts. -/
  inlineHandledInvariants : Std.HashSet Nat := {}

/--
Generate verification conditions for a goal of the form `P ⊢ₛ wp⟦e⟧ Q s₁ ... sₙ` by repeatedly
decomposing `e` using registered `@[spec]` theorems.
Return the VCs and invariant goals.

`stepLimit?`, when `some n`, seeds the fuel counter to `n`; when `none`, fuel is unlimited.
-/
public meta partial def main (goal : MVarId) (ctx : Context) (stepLimit? : Option Nat := none) :
    Grind.GrindM Result := do
  let grindGoal ← Grind.mkGoalCore goal
  let initState : State := { fuel := match stepLimit? with | some n => .limited n | none => .unlimited }
  let ((), state) ← StateRefT'.run (ReaderT.run (work grindGoal) ctx) initState
  _ ← state.invariants.mapIdxM fun idx mv => do
    mv.setTag (Name.mkSimple ("inv" ++ toString (idx + 1)))
  _ ← state.vcs.mapIdxM fun idx mv => do
    mv.setTag (Name.mkSimple ("vc" ++ toString (idx + 1)) ++ (← mv.getTag).eraseMacroScopes)
  let vcs ← state.vcs.filterM (not <$> ·.isAssigned)
  return {
    invariants := state.invariants,
    vcs,
    inlineHandledInvariants := state.inlineHandledInvariants }

end VCGen
