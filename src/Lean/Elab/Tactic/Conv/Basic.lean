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

/--
Annotate `e` with the LHS annotation. The delaborator displays
expressions of the form `lhs = rhs` as `lhs` when they have this annotation.
This is used to implement the infoview for the `conv` mode.
-/
def mkLHSGoal (e : Expr) : MetaM Expr :=
  if let some _ := Expr.eq? e then
    return mkLHSGoalRaw e
  else
    return mkLHSGoalRaw (← whnf e)

/-- Given `lhs`, returns a pair of metavariables `(?rhs, ?newGoal)`
where `?newGoal : lhs = ?rhs`. `tag` is the name of `newGoal`. -/
def mkConvGoalFor (lhs : Expr) (tag : Name := .anonymous) : MetaM (Expr × Expr) := do
  let lhsType ← inferType lhs
  let rhs ← mkFreshExprMVar lhsType
  let targetNew := mkLHSGoalRaw (← mkEq lhs rhs)
  let newGoal ← mkFreshExprSyntheticOpaqueMVar targetNew tag
  return (rhs, newGoal)

def markAsConvGoal (mvarId : MVarId) : MetaM MVarId := do
  let target ← mvarId.getType
  if isLHSGoal? target |>.isSome then
    return mvarId -- it is already tagged as LHS goal
  mvarId.replaceTargetDefEq (← mkLHSGoal (← mvarId.getType))

/-- Given `lhs`, runs the `conv` tactic with the goal `⊢ lhs = ?rhs`.
`conv` should produce no remaining goals that are not solvable with refl.
Returns a pair of instantiated expressions `(?rhs, ?p)` where `?p : lhs = ?rhs`. -/
def convert (lhs : Expr) (conv : TacticM Unit) : TacticM (Expr × Expr) := do
  let (rhs, newGoal) ← mkConvGoalFor lhs
  let savedGoals ← getGoals
  try
    setGoals [newGoal.mvarId!]
    conv
    for mvarId in (← getGoals) do
      liftM <| mvarId.refl <|> mvarId.inferInstance <|> pure ()
    pruneSolvedGoals
    unless (← getGoals).isEmpty do
      throwError "convert tactic failed, there are unsolved goals\n{goalsToMessageData (← getGoals)}"
    pure ()
  finally
    setGoals savedGoals
  return (← instantiateMVars rhs, ← instantiateMVars newGoal)

def getLhsRhsCore (mvarId : MVarId) : MetaM (Expr × Expr) :=
  mvarId.withContext do
    let some (_, lhs, rhs) ← matchEq? (← mvarId.getType) | throwError "invalid 'conv' goal"
    return (lhs, rhs)

def getLhsRhs : TacticM (Expr × Expr) := do
  getLhsRhsCore (← getMainGoal)

def getLhs : TacticM Expr :=
  return (← getLhsRhs).1

def getRhs : TacticM Expr :=
  return (← getLhsRhs).2

/-- `⊢ lhs = rhs` ~~> `⊢ lhs' = rhs` using `h : lhs = lhs'`. -/
def updateLhs (lhs' : Expr) (h : Expr) : TacticM Unit := do
  let mvarId ← getMainGoal
  let rhs ← getRhs
  let newGoal ← mkFreshExprSyntheticOpaqueMVar (mkLHSGoalRaw (← mkEq lhs' rhs)) (← mvarId.getTag)
  mvarId.assign (← mkEqTrans h newGoal)
  replaceMainGoal [newGoal.mvarId!]

/-- Replace `lhs` with the definitionally equal `lhs'`. -/
def changeLhs (lhs' : Expr) : TacticM Unit := do
  let rhs ← getRhs
  liftMetaTactic1 fun mvarId => do
    mvarId.replaceTargetDefEq (mkLHSGoalRaw (← mkEq lhs' rhs))

@[builtin_tactic Lean.Parser.Tactic.Conv.whnf] def evalWhnf : Tactic := fun _ =>
   withMainContext do
     changeLhs (← whnf (← getLhs))

@[builtin_tactic Lean.Parser.Tactic.Conv.reduce] def evalReduce : Tactic := fun _ =>
   withMainContext do
     changeLhs (← reduce (← getLhs))

@[builtin_tactic Lean.Parser.Tactic.Conv.zeta] def evalZeta : Tactic := fun _ =>
   withMainContext do
     changeLhs (← zetaReduce (← getLhs))

/-- Evaluate `sepByIndent conv "; " -/
def evalSepByIndentConv (stx : Syntax) : TacticM Unit := do
  for arg in stx.getArgs, i in [:stx.getArgs.size] do
    if i % 2 == 0 then
      evalTactic arg
    else
      saveTacticInfoForToken arg

@[builtin_tactic Lean.Parser.Tactic.Conv.convSeq1Indented] def evalConvSeq1Indented : Tactic := fun stx => do
  evalSepByIndentConv stx[0]

@[builtin_tactic Lean.Parser.Tactic.Conv.convSeqBracketed] def evalConvSeqBracketed : Tactic := fun stx => do
  let initInfo ← mkInitialTacticInfo stx[0]
  withRef stx[2] <| closeUsingOrAdmit do
    -- save state before/after entering focus on `{`
    withInfoContext (pure ()) initInfo
    evalSepByIndentConv stx[1]
    evalTactic (← `(tactic| all_goals (try rfl)))

@[builtin_tactic Lean.Parser.Tactic.Conv.nestedConv] def evalNestedConv : Tactic := fun stx => do
  evalConvSeqBracketed stx[0]

@[builtin_tactic Lean.Parser.Tactic.Conv.convSeq] def evalConvSeq : Tactic := fun stx => do
  evalTactic stx[0]

@[builtin_tactic Lean.Parser.Tactic.Conv.convConvSeq] def evalConvConvSeq : Tactic := fun stx =>
  withMainContext do
    let (lhsNew, proof) ← convert (← getLhs) (evalTactic stx[2][0])
    updateLhs lhsNew proof

@[builtin_tactic Lean.Parser.Tactic.Conv.paren] def evalParen : Tactic := fun stx =>
  evalTactic stx[1]

/-- Mark goals of the form `⊢ a = ?m ..` with the conv goal annotation -/
def remarkAsConvGoal : TacticM Unit := do
  let newGoals ← (← getUnsolvedGoals).mapM fun mvarId => mvarId.withContext do
    let target ← mvarId.getType
    if let some (_, _, rhs) ← matchEq? target then
      if rhs.getAppFn.isMVar then
        mvarId.replaceTargetDefEq (← mkLHSGoal target)
      else
        return mvarId
    else
      return mvarId
  setGoals newGoals

@[builtin_tactic Lean.Parser.Tactic.Conv.nestedTacticCore] def evalNestedTacticCore : Tactic := fun stx => do
  let seq := stx[2]
  evalTactic seq; remarkAsConvGoal

@[builtin_tactic Lean.Parser.Tactic.Conv.nestedTactic] def evalNestedTactic : Tactic := fun stx => do
  let seq := stx[2]
  let target ← getMainTarget
  if let some _ := isLHSGoal? target then
    liftMetaTactic1 fun mvarId =>
      mvarId.replaceTargetDefEq target.mdataExpr!
  focus do evalTactic seq; remarkAsConvGoal

@[builtin_tactic Lean.Parser.Tactic.Conv.convTactic] def evalConvTactic : Tactic := fun stx =>
  evalTactic stx[2]

private def convTarget (conv : Syntax) : TacticM Unit := withMainContext do
   let target ← getMainTarget
   let (targetNew, proof) ← convert target (withTacticInfoContext (← getRef) (evalTactic conv))
   liftMetaTactic1 fun mvarId => mvarId.replaceTargetEq targetNew proof
   evalTactic (← `(tactic| try rfl))

private def convLocalDecl (conv : Syntax) (hUserName : Name) : TacticM Unit := withMainContext do
   let localDecl ← getLocalDeclFromUserName hUserName
   let (typeNew, proof) ← convert localDecl.type (withTacticInfoContext (← getRef) (evalTactic conv))
   liftMetaTactic1 fun mvarId =>
     return some (← mvarId.replaceLocalDecl localDecl.fvarId typeNew proof).mvarId

@[builtin_tactic Lean.Parser.Tactic.Conv.conv] def evalConv : Tactic := fun stx => do
  match stx with
  | `(tactic| conv%$tk $[at $loc?]? in $(occs)? $p =>%$arr $code) =>
    evalTactic (← `(tactic| conv%$tk $[at $loc?]? =>%$arr pattern $(occs)? $p; ($code:convSeq)))
  | `(tactic| conv%$tk $[at $loc?]? =>%$arr $code) =>
    -- show initial conv goal state between `conv` and `=>`
    withRef (mkNullNode #[tk, arr]) do
      if let some loc := loc? then
        convLocalDecl code loc.getId
      else
        convTarget code
  | _ => throwUnsupportedSyntax

@[builtin_tactic Lean.Parser.Tactic.Conv.first] partial def evalFirst : Tactic :=
  Tactic.evalFirst

end Lean.Elab.Tactic.Conv
