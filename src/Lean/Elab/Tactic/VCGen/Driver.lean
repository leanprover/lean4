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
import Lean.Elab.Do.Basic
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
`work` to enqueue, and the alternatives of the invariant subgoals. Elaborating here ensures
dependent VCs see `?inv` assigned by the time they reach `emitVC`. -/
def handleInvariantSubgoals (subgoals : List MVarId) :
    VCGenM (Array MVarId × Array (Syntax × MVarId)) := do
  let env ← getEnv
  let mut others : Array MVarId := #[]
  let mut alts : Array (Syntax × MVarId) := #[]
  for sg in subgoals do
    if isSpecInvariantType env (← sg.getType) then
      let n := (← get).invariants.size + 1
      modify fun s => { s with invariants := s.invariants.push sg }
      if let some alt := (← read).invariantAlts[n]? then
        alts := alts.push (alt, sg)
      unless ← elabInvariant (← read) n sg do
        sg.setKind .syntheticOpaque
    else
      others := others.push sg
  return (others, alts)

/-- Simplify the target of a verification condition with `Context.simpMethods`. -/
def simpVC (goal : MVarId) : VCGenM Sym.SimpGoalResult := goal.withContext do
  let some methods := (← read).simpMethods | return .noProgress
  let target ← goal.getType
  (← runSimp methods (Sym.Simp.simp target)).toSimpGoalResult goal

/-- The annotation of the note ref `ref` that the verification condition `goal` belongs to: the
first annotation after the first whose term occurs in the target of `goal`, and otherwise the first
annotation. -/
def notePart (ref : Nat) (goal : MVarId) : VCGenM Nat := do
  if ref == 0 then return 0
  let some noteRef := (← get).noteRefs[ref - 1]? | return 0
  if noteRef.parts.size ≤ 1 then return 0
  let target ← instantiateMVarsS (← goal.getType)
  for h : i in 1...noteRef.parts.size do
    let term ← instantiateMVarsS noteRef.parts[i].2
    if (target.find? (· == term)).isSome then return i
  return 0

/--
Called when decomposing the goal further did not succeed; in this case we emit a VC for the goal.
`simp` rewrites the VC only when `reason` says that nothing is left to decompose, so a VC that
`until`, a missing spec or the step limit leaves behind keeps its program as written.
Invariant subgoals are handled separately by `handleInvariantSubgoals` directly inside `work`,
so they never reach this path.
-/
public def emitVC (goal : Grind.Goal) (reason : SolveResult.StopReason) (ref : Nat) :
    VCGenM Unit := do
  -- The annotation is chosen before `simp` rewrites the target, which can remove the term of the
  -- annotation.
  let ref := (ref, ← notePart ref goal.mvarId)
  let mut goal := { goal with mvarId := ← elimTopPre goal.mvarId }
  if reason matches .noEntailment .. | .noProgress .. then
    -- An invariant from an `invariants` alternative is assigned while the target is built, as in
    -- `?inv pref suff (a, b)`. Instantiating it lets `simp` reduce the body of the invariant.
    let target ← goal.mvarId.getType
    let target' ← instantiateMVarsS target
    unless isSameExpr target target' do
      goal := { goal with mvarId := ← goal.mvarId.replaceTargetDefEqFast target' }
    match ← simpVC goal.mvarId with
    | .closed => return
    | .goal mvarId => goal := { goal with mvarId }
    | .noProgress => pure ()
  goal ← processHypotheses goal
  if goal.inconsistent then return
  let some mvarId ← cleanupVC goal.mvarId | return
  mvarId.setKind .syntheticOpaque
  modify fun s => { s with vcs := s.vcs.push { goal with mvarId }, vcRefs := s.vcRefs.push ref }

structure WorkItem where
  goal : Grind.Goal
  scope : Scope
  /-- The note ref of the goal: `0`, or `i + 1` for `State.noteRefs[i]`. -/
  ref : Nat := 0
  /-- The note ref of the code after the program of the goal, set when the goal opened a note ref.
  The next spec application gives it to its subgoals of the post side. -/
  contRef? : Option Nat := none

/-- Open a note ref that shows the verification conditions of `goal` at the annotations `parts`, and
return it. -/
def openNoteRef (parts : Array (Syntax × Expr)) (goal : MVarId) : VCGenM Nat := do
  let mctx ← getMCtx
  modify fun s => { s with noteRefs := s.noteRefs.push { parts, goal, mctx } }
  return (← get).noteRefs.size

/-- The arguments of the program of `info` that carry a `do` note, each with the annotations of its
note and without the note. Spec application removes the note from an argument that becomes the
program of a subgoal. -/
def notedArgs (info : WPApp) : MetaM (Array (Array (Syntax × Expr) × Expr)) :=
  info.prog.getAppArgs.filterMapM fun arg =>
    return (← noteParts? arg).map (·, arg.consumeMData)

/-- The program of the goal `pre ⊑ wp prog post eposts s₁ … sₙ`. -/
def wpProg? (goal : MVarId) : MetaM (Option Expr) := do
  let_expr PartialOrder.rel _ _ _ rhs := (← goal.getType) | return none
  return (isWPApp? rhs).map (·.prog)

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
      emitVC goal reason s.ref
    | .goals scope subgoals note? spec? postSide =>
      -- Handle invariant subgoals eagerly here, so that VC subgoals popped
      -- from the worklist later see the invariant MVar already assigned.
      -- Non-invariant subgoals go to the worklist as usual and will eventually go through `emitVC`.
      let (subgoals, alts) ← handleInvariantSubgoals subgoals
      let mut ref := s.ref
      let mut contRef? := s.contRef?
      if let some parts := note? then
        contRef? := some ref
        ref ← openNoteRef parts goal.mvarId
      unless alts.isEmpty do
        contRef? := some ref
        ref ← openNoteRef (alts.map fun (alt, hole) => (alt, .mvar hole)) goal.mvarId
      let notes ← if let some info := spec? then notedArgs info else pure #[]
      for mv in subgoals.reverse do
        let mut item : WorkItem := { goal := { goal with mvarId := mv }, scope, ref, contRef? }
        if spec?.isSome then
          if let some contRef := contRef? then
            if postSide.contains mv then
              item := { item with ref := contRef }
          item := { item with contRef? := none }
        unless notes.isEmpty do
          if let some prog ← wpProg? mv then
            if let some (parts, _) := notes.find? (·.2 == prog) then
              item := { item with ref := ← openNoteRef parts mv, contRef? := some item.ref }
        worklist := worklist.push item

public structure Result where
  /-- All invariant goals emitted during VC generation, in emit order. The MVarId at
  index `i` carries tag `inv{i+1}`, so callers can treat the array index as the
  invariant number. The entries with an `invariants` alternative are assigned; the caller is
  responsible for filtering before discharging. -/
  invariants : Array MVarId
  /-- Unassigned VCs. Each shares the parent `Grind.Goal`'s state. -/
  vcs : Array Grind.Goal
  /-- The note ref and the annotation of each entry of `vcs`, at the same index (see
  `State.vcRefs`). -/
  vcRefs : Array (Nat × Nat) := #[]
  /-- The note refs that VC generation opened. -/
  noteRefs : Array NoteRef := #[]
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
  let (vcs, vcRefs) := Array.unzip <|
    ← (state.vcs.zip state.vcRefs).filterM fun (g, _) => not <$> g.mvarId.isAssigned
  let unmatchedFrames := state.frameDB.entries.filterMap fun e =>
    if e.retired then none else some e.frameStx
  return {
    invariants := state.invariants,
    vcs,
    vcRefs,
    noteRefs := state.noteRefs,
    unmatchedFrames }


end Lean.Elab.Tactic.VCGen
