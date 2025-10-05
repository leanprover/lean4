/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Elab.Tactic.Grind.Basic
import Init.Grind.Interactive
import Lean.Meta.Tactic.Grind.Solve
import Lean.Meta.Tactic.Grind.Arith.Cutsat.Search
namespace Lean.Elab.Tactic.Grind
/--
Evaluates a tactic script in form of a syntax node with alternating tactics and separators as
children.
-/
partial def evalSepTactics : GrindTactic :=
  goEven
where
  -- `stx[0]` is the next tactic step, if any
  goEven stx := do
    if stx.getNumArgs == 0 then
      return
    let tac := stx[0]
    let stxs := mkNullNode stx.getArgs[1...*]
    evalGrindTactic tac
    goOdd stxs
  -- `stx[0]` is the next separator, if any
  goOdd stx := do
    if stx.getNumArgs == 0 then
      return
    saveTacticInfoForToken stx[0] -- add `TacticInfo` node for `;`
    goEven <| mkNullNode stx.getArgs[1...*]

@[builtin_grind_tactic grindSeq1Indented]
def evalGrindSeq1Indented : GrindTactic := evalSepTactics

@[builtin_grind_tactic grindSeqBracketed]
def evalGrindSeqBracketed : GrindTactic := fun stx => do
  let initInfo ← mkInitialTacticInfo stx[0]
  withRef stx[2] <| closeUsingOrAdmit do
    -- save state before/after entering focus on `{`
    withInfoContext (pure ()) initInfo
    evalSepTactics stx[1]

@[builtin_grind_tactic grindSeq]
def evalGrindSeq : GrindTactic := fun stx =>
  evalGrindTactic stx[0]

@[builtin_grind_tactic Parser.Tactic.Grind.«done»] def evalDone : GrindTactic := fun _ =>
  done

@[builtin_grind_tactic skip] def evalSkip : GrindTactic := fun _ =>
  return ()

open Meta Grind

@[builtin_grind_tactic finish] def evalFinish : GrindTactic := fun _ => do
  let goal ← getMainGoal
  let goal? ← liftGrindM <| solve goal
  replaceMainGoal goal?.toList

@[builtin_grind_tactic lia] def evalLIA : GrindTactic := fun _ => do
  liftGoalM <| discard <| Arith.Cutsat.check

end Lean.Elab.Tactic.Grind
