/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Basic
import Lean.Meta.Tactic.Refl
import Lean.Meta.Tactic.Cases
import Lean.Meta.Tactic.Assumption
import Lean.Meta.Tactic.Simp.Main
import Lean.Meta.SameCtorUtils
public section
namespace Lean.Meta

private def mkAnd? (args : Array Expr) : Option Expr := Id.run do
  if args.isEmpty then
    return none
  else
    let mut result := args.back!
    for arg in args.reverse[1...*] do
      result := mkApp2 (mkConst ``And) arg result
    return result

def elimOptParam (type : Expr) : CoreM Expr := do
  Core.transform type fun e =>
    if e.isAppOfArity ``optParam 2 then
      return TransformStep.visit (e.getArg! 0)
    else
      return .continue

private def mkEqs (args1 args2 : Array Expr) (skipIfPropOrEq : Bool := true) : MetaM (Array Expr) := do
  let mut eqs := #[]
  for arg1 in args1, arg2 in args2 do
    let arg1Type ← inferType arg1
    if !skipIfPropOrEq then
      eqs := eqs.push (← mkEqHEq arg1 arg2)
    else if !(← isProp arg1Type) && arg1 != arg2 then
      eqs := eqs.push (← mkEqHEq arg1 arg2)
  return eqs

private def mkInjectiveTheoremTypeCore? (ctorVal : ConstructorVal) (useEq : Bool) : MetaM (Option Expr) := do
  let us := ctorVal.levelParams.map mkLevelParam
  let type ← elimOptParam ctorVal.type
  forallBoundedTelescope type ctorVal.numParams fun params type =>
  forallTelescope type fun args1 resultType => do
    let k (args2 args2New : Array Expr) : MetaM (Option Expr) := do
      let lhs := mkAppN (mkAppN (mkConst ctorVal.name us) params) args1
      let rhs := mkAppN (mkAppN (mkConst ctorVal.name us) params) args2
      let eq ← mkEq lhs rhs
      let eqs ← mkEqs args1 args2
      if let some andEqs := mkAnd? eqs then
        let result ← if useEq then
          mkEq eq andEqs
        else
          mkArrow eq andEqs
        mkForallFVars params (← mkForallFVars args1 (← mkForallFVars args2New result))
      else
        return none
    let rec mkArgs2 (i : Nat) (type : Expr) (args2 args2New : Array Expr) : MetaM (Option Expr) := do
      if h : i < args1.size then
        let .forallE n d b _  ← whnf type | throwError "unexpected constructor type for `{ctorVal.name}`"
        let arg1 := args1[i]
        if occursOrInType (← getLCtx) arg1 resultType then
          mkArgs2 (i + 1) (b.instantiate1 arg1) (args2.push arg1) args2New
        else
          withLocalDecl n (if useEq then BinderInfo.default else BinderInfo.implicit) d fun arg2 =>
            mkArgs2 (i + 1) (b.instantiate1 arg2) (args2.push arg2) (args2New.push arg2)
      else
        k args2 args2New
    if useEq then
      mkArgs2 0 type #[] #[]
    else
      withImplicitBinderInfos (params ++ args1) do
        mkArgs2 0 type #[] #[]

private def mkInjectiveTheoremType? (ctorVal : ConstructorVal) : MetaM (Option Expr) :=
  mkInjectiveTheoremTypeCore? ctorVal false

private def injTheoremFailureHeader (ctorName : Name) : MessageData :=
  m!"failed to prove injectivity theorem for constructor `{ctorName}`, use 'set_option genInjectivity false' to disable the generation"

private def throwInjectiveTheoremFailure {α} (ctorName : Name) (mvarId : MVarId) : MetaM α :=
  throwError "{injTheoremFailureHeader ctorName}{indentD <| MessageData.ofGoal mvarId}"

private def splitAndAssumption (mvarId : MVarId) (ctorName : Name) : MetaM Unit := do
  (←  mvarId.splitAnd).forM fun mvarId =>
    unless (← mvarId.assumptionCore) do
      throwInjectiveTheoremFailure ctorName mvarId

private def solveEqOfCtorEq (ctorName : Name) (mvarId : MVarId) (h : FVarId) : MetaM Unit := do
  trace[Meta.injective] "solving injectivity goal for {ctorName} with hypothesis {mkFVar h} at\n{mvarId}"
  match (← injection mvarId h) with
  | InjectionResult.solved => unreachable!
  | InjectionResult.subgoal mvarId .. => splitAndAssumption mvarId ctorName

private def mkInjectiveTheoremValue (ctorName : Name) (targetType : Expr) : MetaM Expr :=
  forallTelescopeReducing targetType fun xs type => do
    let mvar ← mkFreshExprSyntheticOpaqueMVar type
    solveEqOfCtorEq ctorName mvar.mvarId! xs.back!.fvarId!
    mkLambdaFVars xs mvar

def mkInjectiveTheoremNameFor (ctorName : Name) : Name :=
  ctorName ++ `inj

private def mkInjectiveTheorem (ctorVal : ConstructorVal) : MetaM Unit := do
  let name := mkInjectiveTheoremNameFor ctorVal.name
  withTraceNode `Meta.injective (msg := (return m!"{exceptEmoji ·} generating `{name}`")) do
  let some type ← mkInjectiveTheoremType? ctorVal
    | return ()
  trace[Meta.injective] "type: {type}"
  let value ← mkInjectiveTheoremValue ctorVal.name type
  addDecl <| Declaration.thmDecl {
    name
    levelParams := ctorVal.levelParams
    type        := (← instantiateMVars type)
    value       := (← instantiateMVars value)
  }

def mkInjectiveEqTheoremNameFor (ctorName : Name) : Name :=
  ctorName ++ `injEq

private def mkInjectiveEqTheoremType? (ctorVal : ConstructorVal) : MetaM (Option Expr) :=
  mkInjectiveTheoremTypeCore? ctorVal true

/--
Collects all components of a nested `And`, as projections.
(Avoids the binders that `MVarId.casesAnd` would introduce.)
-/
private partial def andProjections (e : Expr) : MetaM (Array Expr) := do
  let rec go (e : Expr) (t : Expr) (acc : Array Expr) : MetaM (Array Expr) := do
    match_expr t with
    | And t1 t2 =>
      let acc ← go (mkProj ``And 0 e) t1 acc
      let acc ← go (mkProj ``And 0 e) t2 acc
      return acc
    | _ =>
      return acc.push e
  go e (← inferType e) #[]

private def mkInjectiveEqTheoremValue (ctorName : Name) (targetType : Expr) : MetaM Expr := do
  forallTelescopeReducing targetType fun xs type => do
    let mvar ← mkFreshExprSyntheticOpaqueMVar type
    let [mvarId₁, mvarId₂] ← mvar.mvarId!.apply (mkConst ``Eq.propIntro)
      | throwError "unexpected number of subgoals when proving injective theorem for constructor `{ctorName}`"
    let (h, mvarId₁) ← mvarId₁.intro1
    solveEqOfCtorEq ctorName mvarId₁ h
    let mut mvarId₂ := mvarId₂
    while true do
      let t ← mvarId₂.getType
      let some (conj, body) := t.arrow?  | break
      match_expr conj with
      | And lhs rhs =>
        let [mvarId₂'] ← mvarId₂.applyN (mkApp3 (mkConst `Lean.injEq_helper) lhs rhs body) 1
            | throwError "unexpected number of goals after applying `Lean.and_imp`"
        mvarId₂ := mvarId₂'
      | _ => pure ()
      let (h, mvarId₂') ← mvarId₂.intro1
      (_, mvarId₂) ← substEq mvarId₂' h
    try mvarId₂.refl catch _ => throwError (injTheoremFailureHeader ctorName)
    mkLambdaFVars xs mvar

private def mkInjectiveEqTheorem (ctorVal : ConstructorVal) : MetaM Unit := do
  let name := mkInjectiveEqTheoremNameFor ctorVal.name
  withTraceNode `Meta.injective (msg := (return m!"{exceptEmoji ·} generating `{name}`")) do
  let some type ← mkInjectiveEqTheoremType? ctorVal
    | return ()
  trace[Meta.injective] "type: {type}"
  let value ← mkInjectiveEqTheoremValue ctorVal.name type
  addDecl <| Declaration.thmDecl {
    name
    levelParams := ctorVal.levelParams
    type        := (← instantiateMVars type)
    value       := (← instantiateMVars value)
  }
  addSimpTheorem (ext := simpExtension) name (post := true) (inv := false) AttributeKind.global (prio := eval_prio default)

register_builtin_option genInjectivity : Bool := {
  defValue := true
  descr    := "generate injectivity theorems for inductive datatype constructors. \
    Temporarily (for bootstrapping reasons) also controls the generation of the
    `ctorIdx` definition."
}

def mkInjectiveTheorems (declName : Name) : MetaM Unit := do
  if (← getEnv).contains ``Eq.propIntro && genInjectivity.get (← getOptions) &&  !(← isInductivePredicate declName) then
    withTraceNode `Meta.injective (return m!"{exceptEmoji ·} {declName}") do
    let info ← getConstInfoInduct declName
    unless info.isUnsafe do
      -- We need to reset the local context here because `solveEqOfCtorEq` uses
      -- `assumptionCore`, which can reference "outside" free variables that
      -- were not introduced by `mkInjective(Eq)Theorem` and are not abstracted
      -- by `mkLambdaFVars`, thus adding a declaration with free variables.
      -- See https://github.com/leanprover/lean4/issues/2188
      withLCtx {} {} do
      for ctor in info.ctors do
        withExporting (isExporting := !isPrivateName ctor) do
          let ctorVal ← getConstInfoCtor ctor
          if ctorVal.numFields > 0 then
            mkInjectiveTheorem ctorVal
            mkInjectiveEqTheorem ctorVal

builtin_initialize
  registerTraceClass `Meta.injective

def getCtorAppIndices? (ctorApp : Expr) : MetaM (Option (Array Expr)) := do
  let type ← whnfD (← inferType ctorApp)
  type.withApp fun typeFn typeArgs => do
    let .const declName _ := typeFn | return none
    let .inductInfo val ← getConstInfo declName | return none
    if val.numIndices == 0 then return some #[]
    return some typeArgs[val.numParams...*].toArray

private structure MkHInjTypeResult where
  thmType : Expr
  us : List Level
  numIndices : Nat

private def mkHInjType? (ctorVal : ConstructorVal) : MetaM (Option MkHInjTypeResult) := do
  let us := ctorVal.levelParams.map mkLevelParam
  let type ← elimOptParam ctorVal.type
  forallTelescope type fun args1 _ =>
  withImplicitBinderInfos args1 do
    let params1 := args1[:ctorVal.numParams]
    let k (args2 : Array Expr) : MetaM (Option MkHInjTypeResult) := do
      let params2 := args2[:ctorVal.numParams]
      let lhs := mkAppN (mkConst ctorVal.name us) args1
      let rhs := mkAppN (mkConst ctorVal.name us) args2
      let eq ← mkEqHEq lhs rhs
      let eqs ← mkEqs args1 args2
      if let some andEqs := mkAnd? eqs then
        let result ← mkArrow eq andEqs
        let some idxs1 ← getCtorAppIndices? lhs | return none
        let some idxs2 ← getCtorAppIndices? rhs | return none
        -- **Note**: We dot not skip here because the type of `noConfusion` does not.
        let idxEqs ← mkEqs (params1 ++ idxs1) (params2 ++ idxs2) (skipIfPropOrEq := false)
        let result ← mkArrowN idxEqs result
        let thmType ← mkForallFVars args1 (← mkForallFVars args2 result)
        return some { thmType, us, numIndices := idxs1.size }
      else
        return none
    let rec mkArgs2 (i : Nat) (type : Expr) (args2 : Array Expr) : MetaM (Option MkHInjTypeResult) := do
      if h : i < args1.size then
        let .forallE n d b _  ← whnf type | throwError "unexpected constructor type for `{ctorVal.name}`"
        let arg1 := args1[i]
        withLocalDecl n .implicit d fun arg2 =>
          mkArgs2 (i + 1) (b.instantiate1 arg2) (args2.push arg2)
      else
        k args2
    mkArgs2 0 type #[]

private def failedToGenHInj (ctorVal : ConstructorVal) : MetaM α :=
  throwError "failed to generate heterogeneous injectivity theorem for `{ctorVal.name}`"

private partial def mkHInjectiveTheoremValue? (ctorVal : ConstructorVal) (typeInfo : MkHInjTypeResult) : MetaM (Option Expr) := do
  forallTelescopeReducing typeInfo.thmType fun xs type => do
    let noConfusionName := ctorVal.induct.str "noConfusion"
    let noConfusion := mkConst noConfusionName (0 :: typeInfo.us)
    let noConfusion := mkApp noConfusion type
    let n := xs.size - ctorVal.numParams - typeInfo.numIndices - 1
    let eqs := xs[n...*].toArray
    let eqExprs ← eqs.mapM fun x => do
      match_expr (← inferType x) with
      | Eq _ lhs rhs => return (lhs, rhs)
      | HEq _ lhs _ rhs => return (lhs, rhs)
      | _ => failedToGenHInj ctorVal
    let (args₁, args₂) := eqExprs.unzip
    let noConfusion := mkAppN (mkAppN (mkAppN noConfusion args₁) args₂) eqs
    let .forallE _ d _ _ ← whnf (← inferType noConfusion) | failedToGenHInj ctorVal
    let mvar ← mkFreshExprSyntheticOpaqueMVar d
    let noConfusion := mkApp noConfusion mvar
    let mvarId := mvar.mvarId!
    let (_, mvarId) ← mvarId.intros
    splitAndAssumption mvarId ctorVal.name
    let result ← instantiateMVars noConfusion
    mkLambdaFVars xs result

private def hinjSuffix := "hinj"

def mkHInjectiveTheoremNameFor (ctorName : Name) : Name :=
  ctorName.str hinjSuffix

private def mkHInjectiveTheorem? (thmName : Name) (ctorVal : ConstructorVal) : MetaM (Option TheoremVal) := do
  let some typeInfo ← mkHInjType? ctorVal | return none
  let some value ← mkHInjectiveTheoremValue? ctorVal typeInfo | return none
  return some { name := thmName, value, levelParams := ctorVal.levelParams, type := typeInfo.thmType }

builtin_initialize registerReservedNamePredicate fun env n =>
  match n with
  | .str p "hinj" => (env.find? p matches some (.ctorInfo _))
  | _ => false

builtin_initialize
  registerReservedNameAction fun name => do
    let .str p "hinj" := name | return false
    let some (.ctorInfo ctorVal) := (← getEnv).find? p | return false
    MetaM.run' do
    let some thmVal ← mkHInjectiveTheorem? name ctorVal | return false
    realizeConst p name do
      addDecl (← mkThmOrUnsafeDef thmVal)
    return true

end Lean.Meta
