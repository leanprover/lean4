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
import Lean.Meta.Tactic.Grind.Arith.CommRing.EqCnstr
import Lean.Meta.Tactic.Grind.EMatch
import Lean.Meta.Tactic.Grind.Intro
namespace Lean.Elab.Tactic.Grind

def evalSepTactics (stx : Syntax) : GrindTacticM Unit := do
  for arg in stx.getArgs, i in *...stx.getArgs.size do
    if i % 2 == 0 then
      evalGrindTactic arg
    else
      saveTacticInfoForToken arg

@[builtin_grind_tactic grindSeq1Indented]
def evalGrindSeq1Indented : GrindTactic := fun stx =>
  evalSepTactics stx[0]

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

@[builtin_grind_tactic paren] def evalParen : GrindTactic := fun stx =>
  evalGrindTactic stx[1]

open Meta Grind

@[builtin_grind_tactic finish] def evalFinish : GrindTactic := fun _ => do
  let goal ← getMainGoal
  if let some goal ← liftGrindM <| solve goal then
    let params := (← read).params
    let result ← liftGrindM do mkResult params (some goal)
    throwError "`finish` failed\n{← result.toMessageData}"
  else
    replaceMainGoal []

@[builtin_grind_tactic lia] def evalLIA : GrindTactic := fun _ => do
  liftGoalM <| discard <| Arith.Cutsat.check

@[builtin_grind_tactic ring] def evalRing : GrindTactic := fun _ => do
  liftGoalM <| discard <| Arith.CommRing.check

@[builtin_grind_tactic instantiate] def evalInstantiate : GrindTactic := fun _ => do
  let progress ← liftGoalM <| ematch
  unless progress do
    throwError "`instantiate` tactic failed to instantiate new facts, use `show_patterns` to see active theorems and their patterns."
  let goal ← getMainGoal
  let (goal, _) ← liftGrindM <| withCheapCasesOnly <| SearchM.run goal do
    discard <| assertAll
    getGoal
  replaceMainGoal [goal]

end Lean.Elab.Tactic.Grind
