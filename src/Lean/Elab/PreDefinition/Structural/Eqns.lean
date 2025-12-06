/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Elab.PreDefinition.FixedParams
import Lean.Elab.PreDefinition.EqnsUtils
import Lean.Meta.Tactic.CasesOnStuckLHS
import Lean.Meta.Tactic.Delta
import Lean.Meta.Tactic.Simp.Main
import Lean.Meta.Tactic.Delta
import Lean.Meta.Tactic.CasesOnStuckLHS
import Lean.Meta.Tactic.Split

namespace Lean.Elab
open Meta
open Eqns

namespace Structural

public structure EqnInfo where
  declName    : Name
  levelParams : List Name
  type        : Expr
  value       : Expr
  recArgPos : Nat
  declNames : Array Name
  fixedParamPerms : FixedParamPerms
  deriving Inhabited

/--
Searches in the lhs of goal for a `.brecOn` application, possibly with extra arguments
and under `PProd` projections. Returns the `.brecOn` application and the context
`(fun x => (x).1.2.3 extraArgs = rhs)`.
-/
partial def findBRecOnLHS (goal : Expr) : MetaM (Expr × Expr) := do
  let some (_, lhs, rhs) := goal.eq? | throwError "goal not an equality{indentExpr goal}"
  go lhs fun brecOnApp x c =>
    return (brecOnApp, ← mkLambdaFVars #[x] (← mkEq c rhs))
where
  go {α} (e : Expr) (k : Expr → Expr → Expr → MetaM α) : MetaM α := e.withApp fun f xs => do
    if let .proj t n e := f then
      return ← go e fun brecOnApp x c => k brecOnApp x (mkAppN (mkProj t n c) xs)
    if let .const name _ := f then
      if isBRecOnRecursor (← getEnv) name then
        let arity ← forallTelescope (← inferType f) fun xs _ => return xs.size
        if arity ≤ xs.size then
          let brecOnApp := mkAppN f xs[:arity]
          let extraArgs := xs[arity:]
          return ← withLocalDeclD `x (← inferType brecOnApp) fun x =>
            k brecOnApp x (mkAppN x extraArgs)
    throwError "could not find `.brecOn` application in{indentExpr e}"

def deltaRHS? (mvarId : MVarId) (declName : Name) : MetaM (Option MVarId) := mvarId.withContext do
  let target ← mvarId.getType'
  let some (_, lhs, rhs) := target.eq? | return none
  let some rhs ← delta? rhs.consumeMData (· == declName) | return none
  mvarId.replaceTargetDefEq (← mkEq lhs rhs)

/--
Creates the proof of the unfolding theorem for `declName` with type `type`. It

1. unfolds the function on the left to expose the `.brecOn` application
2. rewrites that using the `.brecOn.eq` theorem, unrolling it once
3. let-binds the last argument, which should be the `.brecOn.go` call of type `.below …`.
   This way subsequent steps (which may involve `simp`) do not touch it and do
   not break the definitional equality with the recursive calls on the RHS.
4. repeatedly splits `match` statements (because on the left we have `match` statements with extra
   `.below` arguments, and on the right we have the original `match` statements) until the goal
   is solved using `rfl` or `contradiction`.
-/
partial def mkProof (declName : Name) (type : Expr) : MetaM Expr := do
  withTraceNode `Elab.definition.structural.eqns (return m!"{exceptEmoji ·} proving:{indentExpr type}") do
    prependError m!"failed to generate equational theorem for `{.ofConstName declName}`" do
    withNewMCtxDepth do
      let main ← mkFreshExprSyntheticOpaqueMVar type
      let (_, mvarId) ← main.mvarId!.intros
      unless (← tryURefl mvarId) do -- catch easy cases
        goUnfold (← deltaLHS mvarId)
      instantiateMVars main
where
  goUnfold (mvarId : MVarId) : MetaM Unit := do
    withTraceNode `Elab.definition.structural.eqns (return m!"{exceptEmoji ·} goUnfold:\n{MessageData.ofGoal mvarId}") do
    let mvarId' ← mvarId.withContext do
      -- This should now be headed by `.brecOn`
      let goal ← mvarId.getType
      let (brecOnApp, context) ← findBRecOnLHS goal
      let brecOnName := brecOnApp.getAppFn.constName!
      let us := brecOnApp.getAppFn.constLevels!
      let brecOnThmName := brecOnName.str "eq"
      let brecOnAppArgs := brecOnApp.getAppArgs
      unless (← hasConst brecOnThmName) do
        throwError "no theorem `{brecOnThmName}`\n{MessageData.ofGoal mvarId}"
      -- We don't just `← inferType eqThmApp` as that beta-reduces more than we want
      let eqThmType ← inferType (mkConst brecOnThmName us)
      let eqThmType ← instantiateForall eqThmType brecOnAppArgs
      let some (_, _, rwRhs) := eqThmType.eq? | throwError "theorem `{brecOnThmName}` is not an equality\n{MessageData.ofGoal mvarId}"
      let recArg := rwRhs.getAppArgs.back!
      trace[Elab.definition.structural.eqns] "abstracting{inlineExpr recArg} from{indentExpr rwRhs}"
      let mvarId2 ← mvarId.define `r (← inferType recArg) recArg
      let (r, mvarId3) ← mvarId2.intro1P
      let mvarId4 ← mvarId3.withContext do
        let goal' := mkApp rwRhs.appFn! (mkFVar r)
        let thm ← mkCongrArg context (mkAppN (mkConst brecOnThmName us) brecOnAppArgs)
        mvarId3.replaceTargetEq (mkApp context goal') thm
      pure mvarId4
    go mvarId'

  go (mvarId : MVarId) : MetaM Unit := do
    withTraceNode `Elab.definition.structural.eqns (return m!"{exceptEmoji ·} step:\n{MessageData.ofGoal mvarId}") do
      if (← tryURefl mvarId) then
        trace[Elab.definition.structural.eqns] "tryURefl succeeded"
        return ()
      else if (← tryContradiction mvarId) then
        trace[Elab.definition.structural.eqns] "tryContadiction succeeded"
        return ()
      else if let some mvarId ← whnfReducibleLHS? mvarId then
        trace[Elab.definition.structural.eqns] "whnfReducibleLHS succeeded"
        go mvarId
      else if let some mvarId ← simpMatch? mvarId then
        trace[Elab.definition.structural.eqns] "simpMatch? succeeded"
        go mvarId
      else if let some mvarId ← simpIf? mvarId (useNewSemantics := true) then
        trace[Elab.definition.structural.eqns] "simpIf? succeeded"
        go mvarId
      else
        let ctx ← Simp.mkContext
        match (← simpTargetStar mvarId ctx (simprocs := {})).1 with
        | TacticResultCNM.closed =>
          trace[Elab.definition.structural.eqns] "simpTargetStar closed the goal"
        | TacticResultCNM.modified mvarId =>
          trace[Elab.definition.structural.eqns] "simpTargetStar modified the goal"
          go mvarId
        | TacticResultCNM.noChange =>
          if let some mvarId ← deltaRHS? mvarId declName then
            trace[Elab.definition.structural.eqns] "deltaRHS? succeeded"
            go mvarId
          else if let some mvarIds ← casesOnStuckLHS? mvarId then
            trace[Elab.definition.structural.eqns] "casesOnStuckLHS? succeeded"
            mvarIds.forM go
          else if let some mvarIds ← splitTarget? mvarId (useNewSemantics := true) then
            trace[Elab.definition.structural.eqns] "splitTarget? succeeded"
            mvarIds.forM go
          else
            throwError "no progress at goal\n{MessageData.ofGoal mvarId}"

public builtin_initialize eqnInfoExt : MapDeclarationExtension EqnInfo ←
  mkMapDeclarationExtension (exportEntriesFn := fun env s _ =>
    -- Do not export for non-exposed defs
    s.filter (fun n _ => env.find? n |>.any (·.hasValue)) |>.toArray)

public def registerEqnsInfo (preDef : PreDefinition) (declNames : Array Name) (recArgPos : Nat)
    (fixedParamPerms : FixedParamPerms) : CoreM Unit := do
  ensureEqnReservedNamesAvailable preDef.declName
  modifyEnv fun env => eqnInfoExt.insert env preDef.declName
    { preDef with recArgPos, declNames, fixedParamPerms }

/-- Generate the "unfold" lemma for `declName`. -/
def mkUnfoldEq (declName : Name) (info : EqnInfo) : MetaM Name := do
  let name := mkEqLikeNameFor (← getEnv) info.declName unfoldThmSuffix
  realizeConst info.declNames[0]! name (doRealize name)
  return name
where
  doRealize name := withOptions (tactic.hygienic.set · false) do
    lambdaTelescope info.value fun xs body => do
      let us := info.levelParams.map mkLevelParam
      let type ← mkEq (mkAppN (Lean.mkConst declName us) xs) body
      let value ← withoutExporting <| mkProof declName type
      let type ← mkForallFVars xs type
      let type ← letToHave type
      let value ← mkLambdaFVars xs value
      addDecl <| Declaration.thmDecl {
        name, type, value
        levelParams := info.levelParams
      }
      inferDefEqAttr name

def getUnfoldFor? (declName : Name) : MetaM (Option Name) := do
  if let some info := eqnInfoExt.find? (← getEnv) declName then
    return some (← mkUnfoldEq declName info)
  else
    return none

@[export lean_get_structural_rec_arg_pos]
def getStructuralRecArgPosImp? (declName : Name) : CoreM (Option Nat) := do
  let some info := eqnInfoExt.find? (← getEnv) declName | return none
  return some info.recArgPos


builtin_initialize
  registerGetUnfoldEqnFn getUnfoldFor?
  registerTraceClass `Elab.definition.structural.eqns

end Structural
end Lean.Elab
