/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Grind.Types
import Lean.Meta.Tactic.Grind.Intro
import Lean.Meta.Tactic.Grind.Arith

namespace Lean.Meta.Grind

inductive LookaheadStatus where
  | resolved
  | notReady
  | ready
  deriving Inhabited, BEq, Repr

private def checkLookaheadStatus (info : LookaheadInfo) : GoalM LookaheadStatus := do
  match info with
  | .imp e =>
    unless (← isEqTrue e) do return .notReady
    let .forallE _ d b _ := e | unreachable!
    if (← isEqTrue d <||> isEqFalse d) then return .resolved
    unless b.hasLooseBVars do
      if (← isEqTrue b <||> isEqFalse b) then return .resolved
    return .ready
  | .arg a b _ eq =>
    if (← isEqTrue eq <||> isEqFalse eq) then return .resolved
    let is := (← get).split.lookaheadArgPos[(a, b)]? |>.getD []
    let mut j := a.getAppNumArgs
    let mut it_a := a
    let mut it_b := b
    repeat
      unless it_a.isApp && it_b.isApp do return .ready
      j := j - 1
      if j ∉ is then
        let arg_a := it_a.appArg!
        let arg_b := it_b.appArg!
        unless (← isEqv arg_a arg_b) do
          return .notReady
      it_a := it_a.appFn!
      it_b := it_b.appFn!
    return .ready

private def tryLookahead (e : Expr) : GoalM Bool := do
  trace[grind.lookahead.try] "{e}"
  withoutModifyingState do
    return false

private def withLookaheadConfig (x : GrindM α) : GrindM α := do
  withTheReader Grind.Context
    (fun ctx => { ctx with config.qlia := true, cheapEagerCases := true })
    x

def lookahead : GrindTactic := fun goal => do
  unless (← getConfig).lookahead do
    return none
  if goal.split.lookaheads.isEmpty then
    return none
  withLookaheadConfig do
  let (progress, goal) ← GoalM.run goal do
    let mut postponed := []
    let mut progress := false
    let infos := (← get).split.lookaheads
    modify fun s => { s with split.lookaheads := [] }
    for info in infos do
      match (← checkLookaheadStatus info) with
      | .resolved => progress := true
      | .notReady => postponed := info :: postponed
      | .ready =>
        if (← tryLookahead info.getExpr) then
          progress := true
        else
          postponed := info :: postponed
    if progress then
      modify fun s => { s with
        split.lookaheads := s.split.lookaheads ++ postponed.reverse
      }
      return true
    else
      return false
  if progress then
    return some [goal]
  else
    return none

end Lean.Meta.Grind
