/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Lean.Elab.Tactic.Meta
public import Lean.Elab.Tactic.VCGen.Context
public import Lean.Elab.Tactic.VCGen.Solve
public import Lean.Meta.Sym.Grind
import Lean.Elab.Tactic.RenameInaccessibles

open Lean Meta Elab Tactic Sym Sym.Internal Lean.Order
open Lean.Elab.Tactic.Do.SpecAttr

namespace Lean.Elab.Tactic.VCGen

/-!
Worklist driver for `vcgen`. Wraps `solve` with a queue of pending goals
and emits VCs (or invariant holes) for those `solve` cannot decompose further.
-/


/--
Elaborate the `invariants` alternative of the invariant hole `mv` with number `n`, if there is one,
and assign `mv`. In `| inv1 a b => e`, the names `a b` rename the inaccessible hypotheses of `mv`.
Reports elaboration errors and returns whether `mv` is assigned.
-/
public def elabInvariant (ctx : Context) (n : Nat) (mv : MVarId) : SymM Bool := do
  let some alt := ctx.invariantAlts[n]? | return false
  let (names, rhs) ← match alt with
    | `(Lean.Parser.Tactic.invariantDotAlt| · $rhs) => pure (#[], rhs)
    | `(Lean.Parser.Tactic.invariantCaseAlt| | $_tag $names* => $rhs) => pure (names, rhs)
    | _ => return false
  let elabRhs : TermElabM Expr := do
    let mv ← withRef alt[1] <| renameInaccessibles mv names
    mv.withContext <| Term.withSynthesize <| Term.elabTermEnsuringType rhs (← mv.getType)
  try
    -- The surrounding grind context forces reducible transparency, under which the type of `mv`
    -- is not unfolded enough to elaborate `rhs`.
    let val ← Meta.withDefault <| elabRhs.run' ctx.termCtx { levelNames := ctx.levelNames }
    mv.assign (← shareCommon (← unfoldReducible (← instantiateMVars val)))
    return true
  catch ex =>
    logException ex
    return false

/-- Pull invariant subgoals out of `subgoals`: register each in `State.invariants` (1-based stable
index) and elaborate its `invariants` alternative. Returns the remaining non-invariant subgoals for
`work` to enqueue. Elaborating here ensures dependent VCs see `?inv` assigned by the time they reach
`emitVC`. -/
def handleInvariantSubgoals (subgoals : List MVarId) : VCGenM (Array MVarId) := do
  let env ← getEnv
  let mut others : Array MVarId := #[]
  for sg in subgoals do
    if isSpecInvariantType env (← sg.getType) then
      let n := (← get).invariants.size + 1
      modify fun s => { s with invariants := s.invariants.push sg }
      unless ← elabInvariant (← read) n sg do
        sg.setKind .syntheticOpaque
    else
      others := others.push sg
  return others

/--
Called when decomposing the goal further did not succeed; in this case we emit a VC for the goal.
`simp` rewrites the VC only when `reason` says that nothing is left to decompose, so a VC that
`until`, a missing spec or the step limit leaves behind keeps its program as written.
Invariant subgoals are handled separately by `handleInvariantSubgoals` directly inside `work`,
so they never reach this path.
-/
public def emitVC (scope : Scope) (goal : Grind.Goal) (reason : SolveResult.StopReason) :
    VCGenM Unit := do
  let mut goal := { goal with mvarId := ← elimTopPre goal.mvarId }
  if reason matches .noEntailment .. | .noProgress .. then
    -- An invariant from an `invariants` alternative is assigned while the target is built, as in
    -- `?inv pref suff (a, b)`. Instantiating it lets `simp` reduce the body of the invariant.
    let target ← goal.mvarId.getType
    let target' ← instantiateMVarsS target
    unless isSameExpr target target' do
      goal := { goal with mvarId := ← goal.mvarId.replaceTargetDefEqFast target' }
    match ← simpGoalWith scope Sym.Simp.simp goal.mvarId with
    | .closed => return
    | .goal mvarId => goal := { goal with mvarId }
    | .noProgress => pure ()
  goal ← processHypotheses goal
  if goal.inconsistent then return
  let some mvarId ← cleanupVC goal.mvarId | return
  mvarId.setKind .syntheticOpaque
  modify fun s => { s with vcs := s.vcs.push { goal with mvarId } }

structure WorkItem where
  goal : Grind.Goal
  scope : Scope

public def work (scope : Scope) (goal : Grind.Goal) : VCGenM Unit := do
  let mvarId ← preprocessMVar goal.mvarId
  let mut worklist : Array WorkItem := #[{ goal := { goal with mvarId }, scope }]
  while let some s := worklist.back? do
    worklist := worklist.pop
    if ← s.goal.mvarId.isAssigned then continue
    let goal ← processHypotheses { s.goal with mvarId := ← finalizeJoinPoint s.goal.mvarId }
    if goal.inconsistent then continue
    match ← solve s.scope goal.mvarId with
    | .stop reason =>
      emitVC s.scope goal reason
    | .goals scope subgoals =>
      -- Handle invariant subgoals eagerly here, so that VC subgoals popped
      -- from the worklist later see the invariant MVar already assigned.
      -- Non-invariant subgoals go to the worklist as usual and will eventually go through `emitVC`.
      let subgoals ← handleInvariantSubgoals subgoals
      worklist := worklist ++ subgoals.reverse.map (fun mv =>
        { goal := { goal with mvarId := mv }, scope })

public structure Result where
  /-- All invariant goals emitted during VC generation, in emit order. The MVarId at
  index `i` carries tag `inv{i+1}`, so callers can treat the array index as the
  invariant number. The entries with an `invariants` alternative are assigned; the caller is
  responsible for filtering before discharging. -/
  invariants : Array MVarId
  /-- Unassigned VCs. Each shares the parent `Grind.Goal`'s state. -/
  vcs : Array Grind.Goal
  /-- Frame terms of `frames` alternatives whose program pattern matched no program. -/
  unmatchedFrames : Array Syntax := #[]

/--
Generate verification conditions for a goal of the form `pre ⊑ wp e post eposts s₁ ... sₙ` by repeatedly
decomposing `e` using registered `@[spec]` theorems.
Return the VCs and invariant goals.

`stepLimit?`, when `some n`, seeds the fuel counter to `n`; when `none`, fuel is unlimited.
-/
public partial def run (goal : Grind.Goal) (ctx : Context) (scope : Scope)
    (stepLimit? : Option Nat := none) (frameDB : FrameDB := {}) :
    Grind.GrindM Result := do
  let initState : State :=
    { fuel := match stepLimit? with | some n => .limited n | none => .unlimited, frameDB }
  -- VCGen temporarily violates the `SymM` folded-projections invariant: `reduceHead?`
  -- exposes kernel projections in intermediate terms and restores the invariant in its
  -- final result, so the `shareCommon` kernel-projection check is disabled.
  let ((), state) ← Sym.withoutFoldProjsCheck <| StateRefT'.run (ReaderT.run (work scope goal) ctx) initState
  _ ← state.invariants.mapIdxM fun idx mv => do
    mv.setTag (Name.mkSimple ("inv" ++ toString (idx + 1)))
  _ ← state.vcs.mapIdxM fun idx g => do
    g.mvarId.setTag (Name.mkSimple ("vc" ++ toString (idx + 1)) ++ (← g.mvarId.getTag).eraseMacroScopes)
  let vcs ← state.vcs.filterM (not <$> ·.mvarId.isAssigned)
  let unmatchedFrames := state.frameDB.entries.filterMap fun e =>
    if e.retired then none else some e.frameStx
  return {
    invariants := state.invariants,
    vcs,
    unmatchedFrames }


end Lean.Elab.Tactic.VCGen
