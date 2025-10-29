/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Elab.Tactic.Grind.Basic
import Lean.Elab.Tactic.Grind.Config
import Init.Grind.Interactive
import Lean.Meta.Tactic.TryThis
import Lean.Meta.Tactic.Grind.Action
import Lean.Meta.Tactic.Grind.EMatchAction
import Lean.Meta.Tactic.Grind.Split
namespace Lean.Elab.Tactic.Grind
open Meta
open Meta.Grind

def withTracing (x : GrindTacticM α) : GrindTacticM α := do
  withReader (fun ctx => { ctx with ctx.config.trace := true }) x

def mkFinish (maxIterations : Nat) : IO Action := do
  let solvers ← Solvers.mkAction
  let step : Action := Action.done <|> solvers <|> Action.instantiate <|> Action.splitNext <|> Action.mbtc
  return Action.checkTactic (warnOnly := true) >> step.loop maxIterations

def maxIterations := 1000 -- **TODO**: Add option

@[builtin_grind_tactic finishTrace] def evalFinishTrace : GrindTactic := fun stx => do
  let `(grind| finish? $[$configItems]*) := stx | throwUnsupportedSyntax
  withConfigItems configItems do
    let a ← mkFinish maxIterations
    let goal ← getMainGoal
    withTracing do
    match (← liftGrindM <| a.run goal) with
    | .closed seq =>
      replaceMainGoal []
      let seq := Action.mkGrindSeq seq
      Tactic.TryThis.addSuggestion stx { suggestion := .tsyntax seq }
    | .stuck gs =>
      let goal :: _ := gs | throwError "`finish?` failed, but resulting goal is not available"
      let params := (← read).params
      let result ← liftGrindM do mkResult params (some goal)
      throwError "`finish?` failed\n{← result.toMessageData}"

end Lean.Elab.Tactic.Grind
