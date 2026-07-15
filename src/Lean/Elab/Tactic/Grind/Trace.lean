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
  withParams (← read).params params only.isSome do
    let a ← Action.mkFinish
    let goal ← getMainGoal
    let params := (← read).params
    let sym := (← read).sym
    withTracing do
    let solved ← liftGrindM do
      let saved ← saveState
      let (initSeq, goal') ← if sym then symInit goal else pure ([], goal)
      match (← a.run goal') with
      | .closed seq =>
        let seq := initSeq ++ seq
        let finishTac ← mkFinishTactic seq
        let seq := Action.mkGrindSeq seq
        if (← Action.checkSeqAt saved goal [finishTac]) then
          Tactic.TryThis.addSuggestions stx #[
            { suggestion := .tsyntax seq },
            { suggestion := .tsyntax finishTac }
          ]
        else
          Tactic.TryThis.addSuggestion stx { suggestion := .tsyntax seq }
        return true
      | .stuck gs =>
        let goal :: _ := gs | throwError "`finish?` failed, but resulting goal is not available"
        let result ← mkResult params (some goal)
        throwError "`finish?` failed\n{← result.toMessageData}"
        return false
    if solved then
      replaceMainGoal []

end Lean.Elab.Tactic.Grind
