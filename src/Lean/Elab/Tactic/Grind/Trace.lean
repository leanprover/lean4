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
namespace Lean.Elab.Tactic.Grind
open Meta
open Meta.Grind

def withTracing (x : GrindTacticM α) : GrindTacticM α := do
  withReader (fun ctx => { ctx with ctx.config.trace := true }) x

@[builtin_grind_tactic finishTrace] def evalFinishTrace : GrindTactic := fun stx => do
  let `(grind| finish? $[$configItems]* $[only%$only]? $[[$params?,*]]?) := stx | throwUnsupportedSyntax
  withConfigItems configItems do
  let params := params?.getD {}
  withParams (← read).params params only.isSome do
    let a ← Action.mkFinish
    let goal ← getMainGoal
    let params := (← read).params
    withTracing do
    let solved ← liftGrindM do
      let saved ← saveState
      match (← a.run goal) with
      | .closed seq =>
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
