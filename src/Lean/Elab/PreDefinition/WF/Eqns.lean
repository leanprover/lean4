/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Tactic.Rewrite
import Lean.Meta.Tactic.Split
import Lean.Elab.PreDefinition.Basic
import Lean.Elab.PreDefinition.Eqns

namespace Lean.Elab.WF
open Meta
open Eqns

structure EqnInfo extends EqnInfoCore where
  declNames       : Array Name
  declNameNonRec  : Name
  fixedPrefixSize : Nat
  deriving Inhabited

private partial def deltaLHSUntilFix (mvarId : MVarId) : MetaM MVarId := mvarId.withContext do
  let target ← mvarId.getType'
  let some (_, lhs, _) := target.eq? | throwTacticEx `deltaLHSUntilFix mvarId "equality expected"
  if lhs.isAppOf ``WellFounded.fix then
    return mvarId
  else
    deltaLHSUntilFix (← deltaLHS mvarId)

private def rwFixEq (mvarId : MVarId) : MetaM MVarId := mvarId.withContext do
  let target ← mvarId.getType'
  let some (_, lhs, rhs) := target.eq? | unreachable!
  let h := mkAppN (mkConst ``WellFounded.fix_eq lhs.getAppFn.constLevels!) lhs.getAppArgs
  let some (_, _, lhsNew) := (← inferType h).eq? | unreachable!
  let targetNew ← mkEq lhsNew rhs
  let mvarNew ← mkFreshExprSyntheticOpaqueMVar targetNew
  mvarId.assign (← mkEqTrans h mvarNew)
  return mvarNew.mvarId!

private def hasWellFoundedFix (e : Expr) : Bool :=
  Option.isSome <| e.find? (·.isConstOf ``WellFounded.fix)

/--
  Helper function for decoding the packed argument for a `WellFounded.fix` application.
  Recall that we use `PSum` and `PSigma` for packing the arguments of mutually recursive nary functions.
-/
private partial def decodePackedArg? (info : EqnInfo) (e : Expr) : Option (Name × Array Expr) := do
  if info.declNames.size == 1 then
    let args := decodePSigma e #[]
    return (info.declNames[0]!, args)
  else
    decodePSum? e 0
where
  decodePSum? (e : Expr) (i : Nat) : Option (Name × Array Expr) := do
    if e.isAppOfArity ``PSum.inl 3 then
      decodePSum? e.appArg! i
    else if e.isAppOfArity ``PSum.inr 3 then
      decodePSum? e.appArg! (i+1)
    else
      guard (i < info.declNames.size)
      return (info.declNames[i]!, decodePSigma e #[])

  decodePSigma (e : Expr) (acc : Array Expr) : Array Expr :=
    /- TODO: check arity of the given function. If it takes a PSigma as the last argument,
       this function will produce incorrect results. -/
    if e.isAppOfArity ``PSigma.mk 4 then
       decodePSigma e.appArg! (acc.push e.appFn!.appArg!)
    else
       acc.push e

/--
  Try to fold `WellFounded.fix` applications that represent recursive applications of the functions in `info.declNames`.
  We need that to make sure `simpMatchWF?` succeeds at goals such as
  ```lean
  ...
  h : g x = 0
  ...
  |- (match (WellFounded.fix ...) with | ...) = ...
  ```
  where `WellFounded.fix ...` can be folded back to `g x`.
-/
private def tryToFoldWellFoundedFix (info : EqnInfo) (us : List Level) (fixedPrefix : Array Expr) (e : Expr) : MetaM Expr := do
  if hasWellFoundedFix e then
    transform e (pre := pre)
  else
    return e
where
  pre (e : Expr) : MetaM TransformStep := do
    let e' := e.headBeta
    if e'.isAppOf ``WellFounded.fix && e'.getAppNumArgs >= 6 then
      let args := e'.getAppArgs
      let packedArg := args[5]!
      let extraArgs := args[6:]
      if let some (declName, args) := decodePackedArg? info packedArg then
        let candidate := mkAppN (mkAppN (mkAppN (mkConst declName us) fixedPrefix) args) extraArgs
        trace[Elab.definition.wf] "found nested WF at discr {candidate}"
        if (← withDefault <| isDefEq candidate e) then
          return .visit candidate
    return .continue

/--
  Simplify `match`-expressions when trying to prove equation theorems for a recursive declaration defined using well-founded recursion.
  It is similar to `simpMatch?`, but is also tries to fold `WellFounded.fix` applications occurring in discriminants.
  See comment at `tryToFoldWellFoundedFix`.
-/
def simpMatchWF? (info : EqnInfo) (us : List Level) (fixedPrefix : Array Expr) (mvarId : MVarId) : MetaM (Option MVarId) :=
  mvarId.withContext do
    let target ← instantiateMVars (← mvarId.getType)
    let (targetNew, _) ← Simp.main target (← Split.getSimpMatchContext) (methods := { pre })
    let mvarIdNew ← applySimpResultToTarget mvarId target targetNew
    if mvarId != mvarIdNew then return some mvarIdNew else return none
where
  pre (e : Expr) : SimpM Simp.Step := do
    let some app ← matchMatcherApp? e | return Simp.Step.visit { expr := e }
    if app.discrs.any hasWellFoundedFix then
      let discrsNew ← app.discrs.mapM (tryToFoldWellFoundedFix info us fixedPrefix ·)
      if discrsNew != app.discrs then
        let app := { app with discrs := discrsNew }
        let eNew := app.toExpr
        trace[Elab.definition.wf] "folded discriminants {indentExpr eNew}"
        return Simp.Step.visit { expr := app.toExpr }
    -- First try to reduce matcher
    match (← reduceRecMatcher? e) with
    | some e' => return Simp.Step.done { expr := e' }
    | none    =>
      match (← Simp.simpMatchCore? app e SplitIf.discharge?) with
      | some r => return r
      | none => return Simp.Step.visit { expr := e }

private def tryToFoldLHS? (info : EqnInfo) (us : List Level) (fixedPrefix : Array Expr) (mvarId : MVarId) : MetaM (Option MVarId) :=
  mvarId.withContext do
    let target ← mvarId.getType'
    let some (_, lhs, rhs) := target.eq? | unreachable!
    let lhsNew ← tryToFoldWellFoundedFix info us fixedPrefix lhs
    if lhs == lhsNew then return none
    let targetNew ← mkEq lhsNew rhs
    let mvarNew ← mkFreshExprSyntheticOpaqueMVar targetNew
    mvarId.assign mvarNew
    return mvarNew.mvarId!

/--
  Given a goal of the form `|- f.{us} a_1 ... a_n b_1 ... b_m = ...`, return `(us, #[a_1, ..., a_n])`
  where `f` is a constant named `declName`, and `n = info.fixedPrefixSize`.
-/
private def getFixedPrefix (declName : Name) (info : EqnInfo) (mvarId : MVarId) : MetaM (List Level × Array Expr) := mvarId.withContext do
  let target ← mvarId.getType'
  let some (_, lhs, _) := target.eq? | unreachable!
  let lhsArgs := lhs.getAppArgs
  if lhsArgs.size < info.fixedPrefixSize || !lhs.getAppFn matches .const .. then
    throwError "failed to generate equational theorem for '{declName}', unexpected number of arguments in the equation left-hand-side\n{mvarId}"
  let result := lhsArgs[:info.fixedPrefixSize]
  trace[Elab.definition.wf.eqns] "fixedPrefix: {result}"
  return (lhs.getAppFn.constLevels!, result)

private partial def mkProof (declName : Name) (info : EqnInfo) (type : Expr) : MetaM Expr := do
  trace[Elab.definition.wf.eqns] "proving: {type}"
  withNewMCtxDepth do
    let main ← mkFreshExprSyntheticOpaqueMVar type
    let (_, mvarId) ← main.mvarId!.intros
    let (us, fixedPrefix) ← getFixedPrefix declName info mvarId
    let rec go (mvarId : MVarId) : MetaM Unit := do
      trace[Elab.definition.wf.eqns] "step\n{MessageData.ofGoal mvarId}"
      if (← tryURefl mvarId) then
        return ()
      else if (← tryContradiction mvarId) then
        return ()
      else if let some mvarId ← simpMatchWF? info us fixedPrefix mvarId then
        go mvarId
      else if let some mvarId ← simpIf? mvarId then
        go mvarId
      else if let some mvarId ← whnfReducibleLHS? mvarId then
        go mvarId
      else match (← simpTargetStar mvarId { config.dsimp := false }).1 with
        | TacticResultCNM.closed => return ()
        | TacticResultCNM.modified mvarId => go mvarId
        | TacticResultCNM.noChange =>
          if let some mvarIds ← casesOnStuckLHS? mvarId then
            mvarIds.forM go
          else if let some mvarIds ← splitTarget? mvarId then
            mvarIds.forM go
          else if let some mvarId ← tryToFoldLHS? info us fixedPrefix mvarId then
            go mvarId
          else
            throwError "failed to generate equational theorem for '{declName}'\n{MessageData.ofGoal mvarId}"
    go (← rwFixEq (← deltaLHSUntilFix mvarId))
    instantiateMVars main

def mkEqns (declName : Name) (info : EqnInfo) : MetaM (Array Name) :=
  withOptions (tactic.hygienic.set · false) do
  let baseName := mkPrivateName (← getEnv) declName
  let eqnTypes ← withNewMCtxDepth <| lambdaTelescope info.value fun xs body => do
    let us := info.levelParams.map mkLevelParam
    let target ← mkEq (mkAppN (Lean.mkConst declName us) xs) body
    let goal ← mkFreshExprSyntheticOpaqueMVar target
    mkEqnTypes info.declNames goal.mvarId!
  let mut thmNames := #[]
  for i in [: eqnTypes.size] do
    let type := eqnTypes[i]!
    trace[Elab.definition.wf.eqns] "{eqnTypes[i]!}"
    let name := baseName ++ (`_eq).appendIndexAfter (i+1)
    thmNames := thmNames.push name
    let value ← mkProof declName info type
    let (type, value) ← removeUnusedEqnHypotheses type value
    addDecl <| Declaration.thmDecl {
      name, type, value
      levelParams := info.levelParams
    }
  return thmNames

builtin_initialize eqnInfoExt : MapDeclarationExtension EqnInfo ← mkMapDeclarationExtension

def registerEqnsInfo (preDefs : Array PreDefinition) (declNameNonRec : Name) (fixedPrefixSize : Nat) : CoreM Unit := do
  let declNames := preDefs.map (·.declName)
  modifyEnv fun env =>
    preDefs.foldl (init := env) fun env preDef =>
      eqnInfoExt.insert env preDef.declName { preDef with declNames, declNameNonRec, fixedPrefixSize }

def getEqnsFor? (declName : Name) : MetaM (Option (Array Name)) := do
  if let some info := eqnInfoExt.find? (← getEnv) declName then
    mkEqns declName info
  else
    return none

def getUnfoldFor? (declName : Name) : MetaM (Option Name) := do
  let env ← getEnv
  Eqns.getUnfoldFor? declName fun _ => eqnInfoExt.find? env declName |>.map (·.toEqnInfoCore)

builtin_initialize
  registerGetEqnsFn getEqnsFor?
  registerGetUnfoldEqnFn getUnfoldFor?
  registerTraceClass `Elab.definition.wf.eqns

end Lean.Elab.WF
