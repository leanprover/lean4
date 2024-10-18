/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Elab.Tactic.Simp
import Lean.Elab.Tactic.Conv.Basic
import Lean.HeadIndex

namespace Lean.Elab.Tactic.Conv
open Meta

private def getContext : MetaM Simp.Context := do
  return {
    simpTheorems  := {}
    congrTheorems := (← getSimpCongrTheorems)
    config        := Simp.neutralConfig
  }

partial def matchPattern? (pattern : AbstractMVarsResult) (e : Expr) : MetaM (Option (Expr × Array Expr)) :=
  withNewMCtxDepth do
    /- TODO: check whether the following is a performance bottleneck. If it is, recall that we used `AbstractMVarsResult` to make
       sure we can match the pattern inside of binders. So, it is not needed in most cases. -/
    let (_, _, pattern) ← openAbstractMVarsResult pattern
    let rec go? (e : Expr) : MetaM (Option (Expr × Array Expr)) := do
      if e.toHeadIndex != pattern.toHeadIndex then
        return none
      else if (← isDefEqGuarded pattern e) then
        return some (e, #[])
      else if e.isApp then
        return (← go? e.appFn!).map fun (f, extra) => (f, extra.push e.appArg!)
      else
        return none
    withReducible <| go? e

inductive PatternMatchState where
  /--
  The state corresponding to a `(occs := *)` pattern, which acts like `occs := 1 2 ... n` where
  `n` is the total number of pattern matches.
  * `subgoals` is the list of subgoals for patterns already matched
  -/
  | all (subgoals : Array MVarId)
  /--
  The state corresponding to a partially consumed `(occs := a₁ a₂ ...)` pattern.
  * `subgoals` is the list of subgoals for patterns already matched,
    along with their index in the original occs list
  * `idx` is the number of matches that have occurred so far
  * `remaining` is a list of `(i, orig)` pairs representing matches we have not yet reached.
    We maintain the invariant that `idx :: remaining.map (·.1)` is sorted.
    The number `i` is the value in the `occs` list and `orig` is its index in the list.
  -/
  | occs (subgoals : Array (Nat × MVarId)) (idx : Nat) (remaining : List (Nat × Nat))

namespace PatternMatchState

/-- Is this pattern no longer interested in accepting matches? -/
def isDone : PatternMatchState → Bool
  | .all _ => false
  | .occs _ _ remaining => remaining.isEmpty

/-- Is this pattern interested in accepting the next match? -/
def isReady : PatternMatchState → Bool
  | .all _ => true
  | .occs _ idx ((i, _) :: _) => idx == i
  | _ => false

/-- Assuming `isReady` returned false, this advances to the next match. -/
def skip : PatternMatchState → PatternMatchState
  | .occs subgoals idx remaining => .occs subgoals (idx + 1) remaining
  | s => s

/--
Assuming `isReady` returned true, this adds the generated subgoal to the list
and advances to the next match.
-/
def accept (mvarId : MVarId) : PatternMatchState → PatternMatchState
  | .all subgoals => .all (subgoals.push mvarId)
  | .occs subgoals idx ((_, n) :: remaining) => .occs (subgoals.push (n, mvarId)) (idx + 1) remaining
  | s => s

end PatternMatchState

private def pre (pattern : AbstractMVarsResult) (state : IO.Ref PatternMatchState) (e : Expr) : SimpM Simp.Step := do
  if (← state.get).isDone then
    return Simp.Step.done { expr := e }
  else if let some (e, extraArgs) ← matchPattern? pattern e then
    if (← state.get).isReady then
      let (rhs, newGoal) ← mkConvGoalFor e
      state.modify (·.accept newGoal.mvarId!)
      let mut proof := newGoal
      for extraArg in extraArgs do
        proof ← mkCongrFun proof extraArg
      return Simp.Step.done { expr := mkAppN rhs extraArgs, proof? := proof }
    else
      state.modify (·.skip)
      -- Note that because we return `visit` here and `done` in the other case,
      -- it is possible for skipping an earlier match to affect what later matches
      -- refer to. For example, matching `f _` in `f (f a) = f b` with occs `[1, 2]`
      -- yields `[f (f a), f b]`, but `[2, 3]` yields `[f a, f b]`, and `[1, 3]` is an error.
      return Simp.Step.continue
  else
    return Simp.Step.continue

@[builtin_tactic Lean.Parser.Tactic.Conv.pattern] def evalPattern : Tactic := fun stx => withMainContext do
  match stx with
  | `(conv| pattern $[(occs := $occs)]? $p) =>
    let patternA ←
       withTheReader Term.Context (fun ctx => { ctx with ignoreTCFailures := true }) <|
       Term.withoutModifyingElabMetaStateWithInfo <| withRef p <|
       Term.withoutErrToSorry do
         abstractMVars (← Term.elabTerm p none)
    let lhs ← getLhs
    let occs ← match occs with
    | none => pure (.occs #[] 0 [(0, 0)])
    | some occs => match occs with
      | `(Parser.Tactic.Conv.occsWildcard| *) => pure (.all #[])
      | `(Parser.Tactic.Conv.occsIndexed| $ids*) => do
        let ids ← ids.mapIdxM fun i id =>
          match id.getNat with
          | 0 => throwErrorAt id "positive integer expected"
          | n+1 => pure (n, i)
        let ids := ids.qsort (·.1 < ·.1)
        unless @Array.allDiff _ ⟨(·.1 == ·.1)⟩ ids do
          throwError "occurrence list is not distinct"
        pure (.occs #[] 0 ids.toList)
      | _ => throwUnsupportedSyntax
    let state ← IO.mkRef occs
    let ctx := { ← getContext with config.memoize := occs matches .all _ }
    let (result, _) ← Simp.main lhs ctx (methods := { pre := pre patternA state })
    let subgoals ← match ← state.get with
    | .all #[] | .occs _ 0 _ =>
      throwError "'pattern' conv tactic failed, pattern was not found{indentExpr patternA.expr}"
    | .all subgoals => pure subgoals
    | .occs subgoals idx remaining =>
      if let some (i, _) := remaining.getLast? then
        throwError "'pattern' conv tactic failed, pattern was found only {idx} times but {i+1} expected"
      pure <| (subgoals.qsort (·.1 < ·.1)).map (·.2)
    (← getRhs).mvarId!.assign result.expr
    (← getMainGoal).assign (← result.getProof)
    replaceMainGoal subgoals.toList
  | _ => throwUnsupportedSyntax
