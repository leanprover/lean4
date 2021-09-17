/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Reduce
import Lean.Meta.Tactic.Apply
import Lean.Meta.Tactic.Replace
import Lean.Elab.Tactic.Basic
import Lean.Elab.Tactic.BuiltinTactic

namespace Lean.Elab.Tactic.Conv
open Meta

def mkConvGoalFor (lhs : Expr) : MetaM (Expr × Expr) := do
  let lhsType ← inferType lhs
  let rhs ← mkFreshExprMVar lhsType
  let targetNew := mkLHSGoal (← mkEq lhs rhs)
  let newGoal ← mkFreshExprSyntheticOpaqueMVar targetNew
  return (rhs, newGoal)

def markAsConvGoal (mvarId : MVarId) : MetaM MVarId := do
  let target ← getMVarType mvarId
  if isLHSGoal? target |>.isSome then
    return mvarId -- it is already tagged as LHS goal
  replaceTargetDefEq mvarId (mkLHSGoal (← getMVarType mvarId))

def convert (lhs : Expr) (conv : TacticM Unit) : TacticM (Expr × Expr) := do
  let (rhs, newGoal) ← mkConvGoalFor lhs
  let savedGoals ← getGoals
  try
    setGoals [newGoal.mvarId!]
    conv
    for mvarId in (← getGoals) do
      try
        applyRefl mvarId
      catch _ =>
        pure ()
    pruneSolvedGoals
    unless (← getGoals).isEmpty do
      throwError "convert tactic failed, there are unsolved goals\n{goalsToMessageData (← getGoals)}"
    pure ()
  finally
    setGoals savedGoals
  return (← instantiateMVars rhs, ← instantiateMVars newGoal)

def getLhsRhsCore (mvarId : MVarId) : MetaM (Expr × Expr) :=
  withMVarContext mvarId do
    let some (_, lhs, rhs) ← matchEq? (← getMVarType mvarId) | throwError "invalid 'conv' goal"
    return (lhs, rhs)

def getLhsRhs : TacticM (Expr × Expr) := do
  getLhsRhsCore (← getMainGoal)

def getLhs : TacticM Expr :=
  return (← getLhsRhs).1

def getRhs : TacticM Expr :=
  return (← getLhsRhs).2

/-- `⊢ lhs = rhs` ~~> `⊢ lhs' = rhs` using `h : lhs = lhs'`. -/
def updateLhs (lhs' : Expr) (h : Expr) : TacticM Unit := do
  let rhs ← getRhs
  let newGoal ← mkFreshExprSyntheticOpaqueMVar (mkLHSGoal (← mkEq lhs' rhs))
  assignExprMVar (← getMainGoal) (← mkEqTrans h newGoal)
  replaceMainGoal [newGoal.mvarId!]

/-- Replace `lhs` with the definitionally equal `lhs'`. -/
def changeLhs (lhs' : Expr) : TacticM Unit := do
  let rhs ← getRhs
  liftMetaTactic1 fun mvarId => do
    replaceTargetDefEq mvarId (mkLHSGoal (← mkEq lhs' rhs))

@[builtinTactic Lean.Parser.Tactic.Conv.whnf] def evalWhnf : Tactic := fun stx =>
   withMainContext do
     changeLhs (← whnf (← getLhs))

@[builtinTactic Lean.Parser.Tactic.Conv.reduce] def evalReduce : Tactic := fun stx =>
   withMainContext do
     changeLhs (← reduce (← getLhs))

@[builtinTactic Lean.Parser.Tactic.Conv.convSeq1Indented] def evalConvSeq1Indented : Tactic := fun stx => do
  evalTacticSeq1Indented stx

@[builtinTactic Lean.Parser.Tactic.Conv.convSeqBracketed] def evalConvSeqBracketed : Tactic := fun stx => do
  let initInfo ← mkInitialTacticInfo stx[0]
  withRef stx[2] <| closeUsingOrAdmit do
    -- save state before/after entering focus on `{`
    withInfoContext (pure ()) initInfo
    evalManyTacticOptSemi stx[1]
    evalTactic (← `(tactic| all_goals (try rfl)))

@[builtinTactic Lean.Parser.Tactic.Conv.nestedConv] def evalNestedConv : Tactic := fun stx => do
  evalConvSeqBracketed stx[0]

@[builtinTactic Lean.Parser.Tactic.Conv.convSeq] def evalConvSeq : Tactic := fun stx => do
  evalTactic stx[0]

@[builtinTactic Lean.Parser.Tactic.Conv.paren] def evalParen : Tactic := fun stx =>
  evalTactic stx[1]

/-- Mark goals of the form `⊢ a = ?m ..` with the conv goal annotation -/
def remarkAsConvGoal : TacticM Unit := do
  let newGoals ← (← getUnsolvedGoals).mapM fun mvarId => withMVarContext mvarId do
    let target ← getMVarType mvarId
    if let some (_, lhs, rhs) ← matchEq? target then
      if rhs.getAppFn.isMVar then
        replaceTargetDefEq mvarId (mkLHSGoal target)
      else
        return mvarId
    else
      return mvarId
  setGoals newGoals

@[builtinTactic Lean.Parser.Tactic.Conv.nestedTacticCore] def evalNestedTacticCore : Tactic := fun stx => do
  let seq := stx[2]
  evalTactic seq; remarkAsConvGoal

@[builtinTactic Lean.Parser.Tactic.Conv.nestedTactic] def evalNestedTactic : Tactic := fun stx => do
  let seq := stx[2]
  let target ← getMainTarget
  if let some _ := isLHSGoal? target then
    liftMetaTactic1 fun mvarId =>
      replaceTargetDefEq mvarId target.mdataExpr!
  focus do evalTactic seq; remarkAsConvGoal

private def convTarget (conv : Syntax) : TacticM Unit := withMainContext do
   let target ← getMainTarget
   let (targetNew, proof) ← convert target (evalTactic conv)
   liftMetaTactic1 fun mvarId => replaceTargetEq mvarId targetNew proof
   evalTactic (← `(tactic| try rfl))

private def convLocalDecl (conv : Syntax) (hUserName : Name) : TacticM Unit := withMainContext do
   let localDecl ← getLocalDeclFromUserName hUserName
   let (typeNew, proof) ← convert localDecl.type (evalTactic conv)
   liftMetaTactic1 fun mvarId =>
     return some (← replaceLocalDecl mvarId localDecl.fvarId typeNew proof).mvarId

@[builtinTactic Lean.Parser.Tactic.Conv.conv] def evalConv : Tactic := fun stx => do
  match stx with
  | `(tactic| conv $[at $loc?]? in $p => $code) =>
    evalTactic (← `(tactic| conv $[at $loc?]? => pattern $p; ($code:convSeq)))
  | `(tactic| conv $[at $loc?]? => $code) =>
    if let some loc := loc? then
      convLocalDecl code loc.getId
    else
      convTarget code
  | _ => throwUnsupportedSyntax

end Lean.Elab.Tactic.Conv
