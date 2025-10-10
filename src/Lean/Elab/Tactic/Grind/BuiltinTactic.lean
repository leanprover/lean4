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
import Lean.Meta.Tactic.Grind.Arith.Linear.Search
import Lean.Meta.Tactic.Grind.Arith.CommRing.EqCnstr
import Lean.Meta.Tactic.Grind.AC.Eq
import Lean.Meta.Tactic.Grind.EMatch
import Lean.Meta.Tactic.Grind.Intro
import Lean.Meta.Tactic.Grind.Split
import Lean.Meta.Tactic.Grind.Anchor
import Lean.Elab.Tactic.Basic
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

@[builtin_grind_tactic Parser.Tactic.Grind.«sorry»] def evalSorry : GrindTactic := fun _ => do
  let goal ← getMainGoal
  goal.mvarId.admit
  replaceMainGoal []

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

@[builtin_grind_tactic linarith] def evalLinarith : GrindTactic := fun _ => do
  liftGoalM <| discard <| Arith.Linear.check

@[builtin_grind_tactic ring] def evalRing : GrindTactic := fun _ => do
  liftGoalM <| discard <| Arith.CommRing.check

@[builtin_grind_tactic ac] def evalAC : GrindTactic := fun _ => do
  liftGoalM <| discard <| AC.check

@[builtin_grind_tactic instantiate] def evalInstantiate : GrindTactic := fun _ => do
  let progress ← liftGoalM <| ematch
  unless progress do
    throwError "`instantiate` tactic failed to instantiate new facts, use `show_patterns` to see active theorems and their patterns."
  let goal ← getMainGoal
  let (goal, _) ← liftGrindM <| withCheapCasesOnly <| SearchM.run goal do
    discard <| assertAll
    getGoal
  replaceMainGoal [goal]

@[builtin_grind_tactic cases] def evalCases : GrindTactic := fun stx => do
  match stx with
  | `(grind| cases #$anchor:hexnum) =>
    let numDigits := anchor.getHexNumSize
    let val := anchor.getHexNumVal
    if val >= UInt64.size then
      throwError "invalid anchor, value is too big"
    let val := val.toUInt64
    let goal ← getMainGoal
    let candidates := goal.split.candidates
    let (goals, genNew) ← liftSearchM do
      for c in candidates do
        let anchor ← getAnchor c.getExpr
        if isAnchorPrefix numDigits val anchor then
          let some result ← split? c
            | throwError "`cases` tactic failed, case-split is not ready{indentExpr c.getExpr}"
          return result
      throwError "`cases` tactic failed, invalid anchor"
    let goals ← goals.filterMapM fun goal => do
      let (goal, _) ← liftGrindM <| SearchM.run goal do
        intros genNew
        getGoal
      if goal.inconsistent then
        return none
      else
        return some goal
    replaceMainGoal goals
  | _ => throwUnsupportedSyntax

@[builtin_grind_tactic Parser.Tactic.Grind.focus] def evalFocus : GrindTactic := fun stx => do
  let mkInfo ← mkInitialTacticInfo stx[0]
  focus do
    -- show focused state on `focus`
    withInfoContext (pure ()) mkInfo
    evalGrindTactic stx[1]

@[builtin_grind_tactic allGoals] def evalAllGoals : GrindTactic := fun stx => do
  let goals ← getGoals
  let mut goalsNew := #[]
  let mut abort := false
  for goal in goals do
    unless (← goal.mvarId.isAssigned) do
      setGoals [goal]
      let saved ← saveState
      abort ← Grind.tryCatch
        (do
          evalGrindTactic stx[1]
          pure abort)
        (fun ex => do
          if (← read).recover then
            logException ex
            let msgLog ← Core.getMessageLog
            saved.restore
            Core.setMessageLog msgLog
            admitGoal goal.mvarId
            pure true
          else
            throw ex)
      goalsNew := goalsNew ++ (← getUnsolvedGoals)
  if abort then
    throwAbortTactic
  setGoals goalsNew.toList

@[builtin_grind_tactic withAnnotateState] def evalWithAnnotateState : GrindTactic := fun stx =>
  withTacticInfoContext stx[1] do
  evalGrindTactic stx[2]

@[builtin_grind_tactic anyGoals] def evalAnyGoals : GrindTactic := fun stx => do
  let goals ← getGoals
  let mut goalsNew := #[]
  let mut succeeded := false
  for goal in goals do
    unless (← goal.mvarId.isAssigned) do
      setGoals [goal]
      try
        evalGrindTactic stx[1]
        goalsNew := goalsNew ++ (← getUnsolvedGoals)
        succeeded := true
      catch _ =>
        goalsNew := goalsNew.push goal
  unless succeeded do
    throwError "Tactic failed on all goals:{indentD stx[1]}"
  setGoals goalsNew.toList

@[builtin_grind_tactic «next»] def evalNext : GrindTactic := fun stx => do
  match stx with
  | `(grind| next%$nextTk =>%$arr $seq:grindSeq) => do
    let goal :: goals ← getUnsolvedGoals | throwNoGoalsToBeSolved
    setGoals [goal]
    goal.mvarId.setTag Name.anonymous
    withCaseRef arr seq <| closeUsingOrAdmit <| withTacticInfoContext (mkNullNode #[nextTk, arr]) <|
      evalGrindTactic stx[2]
    setGoals goals
  | _ => throwUnsupportedSyntax

@[builtin_grind_tactic nestedTacticCore] def evalNestedTactic : GrindTactic := fun stx => do
  match stx with
  | `(grind| tactic%$tacticTk =>%$arr $seq:tacticSeq) => do
    let goal ← getMainGoal
    let recover := (← read).recover
    discard <| Tactic.run goal.mvarId <| withCaseRef arr seq <| Tactic.closeUsingOrAdmit
      <| Tactic.withTacticInfoContext (mkNullNode #[tacticTk, arr])
      <| Tactic.withRecover recover <| evalTactic seq
    replaceMainGoal []
  | _ => throwUnsupportedSyntax

@[builtin_grind_tactic «first»] partial def evalFirst : GrindTactic := fun stx => do
  let tacs := stx[1].getArgs
  if tacs.isEmpty then throwUnsupportedSyntax
  loop tacs 0
where
  loop (tacs : Array Syntax) (i : Nat) :=
    if i == tacs.size - 1 then
      evalGrindTactic tacs[i]![1]
    else
      evalGrindTactic tacs[i]![1] <|> loop tacs (i+1)

@[builtin_grind_tactic failIfSuccess] def evalFailIfSuccess : GrindTactic := fun stx =>
  Term.withoutErrToSorry <| withoutRecover do
    let tactic := stx[1]
    if (← try evalGrindTactic tactic; pure true catch _ => pure false) then
      throwError "The tactic provided to `fail_if_success` succeeded but was expected to fail:{indentD stx[1]}"

@[builtin_grind_tactic «fail»] def evalFail : GrindTactic := fun stx => do
  let goals ← getGoals
  let goalsMsg := MessageData.joinSep (goals.map (MessageData.ofGoal ·.mvarId)) m!"\n\n"
  match stx with
  | `(grind| fail)          => throwError "Failed: `fail` tactic was invoked\n{goalsMsg}"
  | `(grind| fail $msg:str) => throwError "{msg.getString}\n{goalsMsg}"
  | _ => throwUnsupportedSyntax

end Lean.Elab.Tactic.Grind
