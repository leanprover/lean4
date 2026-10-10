/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Elab.Tactic.Grind.Basic
import Lean.Elab.Tactic.Grind.Config
import Lean.Elab.Tactic.Grind.Param
import Lean.Meta.Tactic.TryThis
import Lean.Meta.Tactic.Grind.Finish
import Lean.Meta.Tactic.Grind.CollectParams
import Lean.Meta.Sym.Grind
namespace Lean.Elab.Tactic.Grind
open Meta
open Meta.Grind

def withTracing (x : GrindTacticM α) : GrindTacticM α := do
  withReader (fun ctx => { ctx with ctx.config.trace := true }) x

/--
In `sym =>` mode, the initialization performed on entry by `grind =>` (introductions +
proof by contradiction + internalization) has not been applied to the goal. The `finish`
action performs equivalent steps internally, but they are not recorded in the resulting
script. This function applies the interactive `intros` and `by_contra` steps, and returns
them so they can be included in the script suggested by `finish?`.
-/
private def symInit (goal : Goal) : GrindM (List TGrind × Goal) := do
  let mut seq : List TGrind := []
  let mut goal := goal
  -- Introduce hypotheses, if any
  let hygienic := tactic.hygienic.get (← getOptions)
  if let .goal _ goalNew ← Goal.intros goal #[] hygienic then
    goal ← Goal.internalizeAll goalNew
    seq := seq ++ [← `(grind| intros)]
  -- Apply proof by contradiction if the target is not already `False`
  let target ← goal.mvarId.getType
  unless target.isFalse do
    let mvarId ← if (← isProp target) then pure goal.mvarId else goal.mvarId.exfalso
    if let some mvarId ← mvarId.byContra? then
      -- `byContra?` produces `⊢ ¬target → False`, introduce the negated hypothesis
      let (_, mvarId) ← mvarId.intro1
      goal ← Goal.internalizeAll { goal with mvarId }
      seq := seq ++ [← `(grind| by_contra)]
  return (seq, goal)

@[builtin_grind_tactic finishTrace] def evalFinishTrace : GrindTactic := fun stx => do
  let `(grind| finish? $[$configItems]* $[only%$only]? $[[$params?,*]]?) := stx | throwUnsupportedSyntax
  withConfigItems configItems do
  let params := params?.getD {}
  let preserved ← getPreservedParams params
  /-
  Suggestions are validated at the goal *before* `withParams` asserts the parameters, i.e.,
  where a replay starts. Validating after would accept suggestions that only work because
  the parameters are active.
  -/
  let goal₀ ← getMainGoal
  let saved₀ ← liftGrindM Meta.Grind.saveState
  withParams (← read).params params only.isSome do
    let a ← Action.mkFinish
    let goal ← getMainGoal
    let params := (← read).params
    let sym := (← read).sym
    withTracing do
    let solved ← liftGrindM do
      let (initSeq, goal') ← if sym then symInit goal else pure ([], goal)
      match (← a.run goal') with
      | .closed seq =>
        let seq := initSeq ++ seq
        let finishTac ← mkFinishTactic seq preserved
        let seqTac := Action.mkGrindSeq seq
        let mut suggestions : Array Tactic.TryThis.Suggestion := #[]
        if (← Action.checkSeqAt saved₀ goal₀ seq) then
          suggestions := suggestions.push { suggestion := .tsyntax seqTac }
        if (← Action.checkSeqAt saved₀ goal₀ [finishTac]) then
          suggestions := suggestions.push { suggestion := .tsyntax finishTac }
        if suggestions.isEmpty then
          /- If `suggestions` is empty, then both `Action.checkSeqAt` calls above have failed and none of the generated tactics could close the goal. -/
          logWarning m!"generated tactic cannot close the goal{indentD (← Action.mkGrindNext seq)}\nInitial goal\n{goal₀.mvarId}"
          suggestions := #[{ suggestion := .tsyntax seqTac }]
        if suggestions.size == 1 then
          Tactic.TryThis.addSuggestion stx suggestions[0]!
        else
          Tactic.TryThis.addSuggestions stx suggestions
        return true
      | .stuck gs =>
        let goal :: _ := gs | throwError "`finish?` failed, but resulting goal is not available"
        let result ← mkResult params (some goal)
        throwError "`finish?` failed\n{← result.toMessageData}"
        return false
    if solved then
      replaceMainGoal []

end Lean.Elab.Tactic.Grind
