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

open Lean Meta Elab Tactic Sym Sym.Internal Lean.Order
open Lean.Elab.Tactic.Do.SpecAttr

namespace Lean.Elab.Tactic.VCGen

/-!
Worklist driver for `vcgen`. Wraps `solve` with a queue of pending goals
and emits VCs (or invariant holes) for those `solve` cannot decompose further.
-/


/--
Try to elaborate the user's invariant alt for invariant number `n` inline,
discharging `mv` if successful. Looks up `Context.invariantAlts[n]?` (pre-parsed
in `Frontend`) and dispatches to `exact $rhs` for bullet form or
`rename_i $args*; exact $rhs` for labelled form. Returns whether elaboration
succeeded. Numbering is 1-based; out-of-order labelled forms (e.g. `| inv2 => …`
before `| inv1 => …`) are supported because the map is keyed by parsed number,
not position.
-/
public def elabInvariant (invariantAlts : Std.HashMap Nat Syntax) (n : Nat) (mv : MVarId) : SymM Bool := do
  try
    let some alt := invariantAlts[n]? | return false
    let tac ← match alt with
      | `(Lean.Parser.Tactic.invariantDotAlt| · $rhs) => `(tactic| exact $rhs)
      | `(Lean.Parser.Tactic.invariantCaseAlt| | $_tag $args* => $rhs) =>
          `(tactic| (rename_i $args*; exact $rhs))
      | _ => return false
    -- `withDefault`: the surrounding grind context forces reducible transparency,
    -- under which the invariant's type isn't resolved enough for term elaboration
    -- of the alternative's right-hand side to succeed.
    withRef alt <| discard <| Meta.withDefault <| Lean.Elab.runTactic mv tac {} {}
    -- The tactic runs without throwing even when it fails to close the goal;
    -- check explicitly that the MVar got assigned.
    if ← mv.isAssigned then
      -- Preprocess the assignment to `mv` because it will interact with the `SymM` world
      if let some val ← getExprMVarAssignment? mv then
        let val ← unfoldReducible val
        let val ← shareCommon val
        mv.assign val
      return true
    else
      return false
  catch _ => return false

/-- Pull invariant subgoals out of `subgoals` and handle them eagerly: register
each in `State.invariants` (1-based stable index) and try to inline-elaborate
its matching user alt. Returns the remaining non-invariant subgoals for `work`
to enqueue. Eager handling here ensures dependent VCs see `?inv` assigned by
the time they reach `emitVC`. -/
private def handleInvariantSubgoals (subgoals : List MVarId) : VCGenM (Array MVarId) := do
  let env ← getEnv
  let mut others : Array MVarId := #[]
  for sg in subgoals do
    if isSpecInvariantType env (← sg.getType) then
      let n := (← get).invariants.size + 1
      modify fun s => { s with invariants := s.invariants.push sg }
      if ← elabInvariant (← read).invariantAlts n sg then
        modify fun s => { s with inlineHandledInvariants := s.inlineHandledInvariants.insert n }
      else
        sg.setKind .syntheticOpaque
    else
      others := others.push sg
  return others

/-- `fun r => binderNameHint r post Q` for the postcondition lambda `post = fun r => Q`, with
`post` itself as the name-carrying binder argument, so the wrap is definitionally equal. `none`
when `post` is not a lambda binding a program name. -/
private def wrapPostHint? (post : Expr) : VCGenM (Option Expr) := do
  let .lam n dom body bi := post | return none
  unless isProgramName n do return none
  let postTy ← Sym.inferType post
  let .forallE _ _ codomain _ := postTy | return none
  if codomain.hasLooseBVars then return none
  let hint ← mkConstS ``binderNameHint
    [← Sym.getLevel dom, ← Sym.getLevel postTy, ← Sym.getLevel codomain]
  return some (.lam n dom (mkApp6 hint dom postTy codomain (.bvar 0) post body) bi)

/-- Replace the `i`-th argument of the application `e` by `v`. -/
private def setAppArg (e : Expr) (i : Nat) (v : Expr) : VCGenM Expr := do
  let args := e.getAppArgs
  mkAppNS e.getAppFn (args.set! i v)

/--
Wrap the goal's postcondition lambda in a `binderNameHint`, so a binder that receives the
program's result takes the name the postcondition binds. Program hints win over this one: hint
resolution keeps the first user-facing name, and the precondition's hints come first. Handles the
three entry shapes: a `Triple`, an entailment into a `wp` application, and a bare `wp` application.
-/
private def hintPostBinder (mvarId : MVarId) : VCGenM MVarId := mvarId.withContext do
  let target := (← mvarId.getType).consumeMData
  let mkWPTarget (wpApp : Expr) (k : Expr → VCGenM Expr) : VCGenM (Option Expr) := do
    let n := wpApp.getAppNumArgs
    unless n ≥ 10 && wpApp.getAppFn.isConstOf ``Std.WP.wp do return none
    let some post ← wrapPostHint? (wpApp.getArg! 8 n) | return none
    return some (← k (← setAppArg wpApp 8 post))
  let newTarget? ← do
    if target.isAppOfArity ``Std.WP.Triple 11 then
      let some post ← wrapPostHint? (target.getArg! 9) | pure none
      pure (some (← setAppArg target 9 post))
    else match_expr target with
      | PartialOrder.rel _ _ _ rhs =>
        mkWPTarget rhs fun rhs' => setAppArg target 3 rhs'
      | _ => mkWPTarget target pure
  let some newTarget := newTarget? | return mvarId
  mvarId.replaceTargetDefEqFast (← shareCommon newTarget)

/--
Called when decomposing the goal further did not succeed; in this case we emit a VC for the goal.
Invariant subgoals are handled separately by `handleInvariantSubgoals` directly inside `work`,
so they never reach this path.
-/
public def emitVC (goal : Grind.Goal) : VCGenM Unit := do
  let mut goal := { goal with mvarId := ← elimTopPre goal.mvarId }
  -- Strip residual hints, such as one applied to a compound value that frame-rule unification
  -- embedded under a wand, so the discharging tactic sees every atom bare.
  let target ← goal.mvarId.getType
  if target.hasBinderNameHint then
    let target' ← liftMetaM <| Expr.resolveBinderNameHint target
    goal := { goal with mvarId := ← goal.mvarId.replaceTargetDefEqFast (← shareCommon target') }
  -- Head-reduce the target: an invariant applied to the initial, stepped or final state leaves a
  -- beta/iota redex such as `match Sum.inl (0, 0) with …` at the head of the VC.
  if let some target' ← reduceHead? (← goal.mvarId.getType) then
    goal := { goal with mvarId := ← goal.mvarId.replaceTargetDefEqFast target' }
  goal ← processHypotheses goal
  if goal.inconsistent then return
  -- `trivial`: when false, skip `solveTrivialConjuncts` (which collapses And-chains via rfl);
  -- emit the goal as-is.
  let mvarId ←
    if (← read).trivial then
      let some mvarId ← solveTrivialConjuncts goal.mvarId | return
      pure mvarId
    else
      pure goal.mvarId
  mvarId.setKind .syntheticOpaque
  modify fun s => { s with vcs := s.vcs.push { goal with mvarId } }

private structure WorkItem where
  goal : Grind.Goal
  scope : Scope

public def work (scope : Scope) (goal : Grind.Goal) : VCGenM Unit := do
  let mvarId ← preprocessMVar goal.mvarId
  let mut worklist : Array WorkItem := #[{ goal := { goal with mvarId }, scope }]
  while let some s := worklist.back? do
    worklist := worklist.pop
    if ← s.goal.mvarId.isAssigned then continue
    let goal ← processHypotheses s.goal
    if goal.inconsistent then continue
    match ← solve s.scope goal.mvarId with
    | .stop _reason =>
      emitVC goal
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
  invariant number. Some entries may already be assigned (inline-elaborated by
  `Driver.emitVC`); the caller is responsible for filtering before discharging. -/
  invariants : Array MVarId
  /-- Unassigned VCs. Each shares the parent `Grind.Goal`'s state. -/
  vcs : Array Grind.Goal
  /-- Invariant numbers handled inline by `Driver.emitVC`. Used by `Frontend` to
  avoid spurious "alt does not match any invariant" warnings for inline-consumed
  alts. -/
  inlineHandledInvariants : Std.HashSet Nat := {}
  /-- Frame terms of `frames` alternatives whose program pattern matched no program. -/
  unmatchedFrames : Array Syntax := #[]

/--
Generate verification conditions for a goal of the form `pre ⊑ wp e post epost s₁ ... sₙ` by repeatedly
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
  let ((), state) ← Sym.withoutFoldProjsCheck <| StateRefT'.run (ReaderT.run (do
      let goal := { goal with mvarId := ← hintPostBinder goal.mvarId }
      work scope goal) ctx) initState
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
    inlineHandledInvariants := state.inlineHandledInvariants,
    unmatchedFrames }


end Lean.Elab.Tactic.VCGen
