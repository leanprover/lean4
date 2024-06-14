/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Transform
import Lean.Meta.Tactic.Injection
import Lean.Meta.Tactic.Apply
import Lean.Meta.Tactic.Cases
import Lean.Meta.Tactic.Subst
import Lean.Meta.Tactic.Simp.Types
import Lean.Meta.Tactic.Assumption

namespace Lean.Meta

private def mkAnd? (args : Array Expr) : Option Expr := do
  if args.isEmpty then
    return none
  else
    let mut result := args.back
    for arg in args.reverse[1:] do
      result := mkApp2 (mkConst ``And) arg result
    return result

def elimOptParam (type : Expr) : CoreM Expr := do
  Core.transform type fun e =>
    if e.isAppOfArity  ``optParam 2 then
      return TransformStep.visit (e.getArg! 0)
    else
      return TransformStep.visit e

private partial def mkInjectiveTheoremTypeCore? (ctorVal : ConstructorVal) (useEq : Bool) : MetaM (Option Expr) := do
  let us := ctorVal.levelParams.map mkLevelParam
  let type ← elimOptParam ctorVal.type
  forallBoundedTelescope type ctorVal.numParams fun params type =>
  forallTelescope type fun args1 resultType => do
    let jp (args2 args2New : Array Expr) : MetaM (Option Expr) := do
      let lhs := mkAppN (mkAppN (mkConst ctorVal.name us) params) args1
      let rhs := mkAppN (mkAppN (mkConst ctorVal.name us) params) args2
      let eq ← mkEq lhs rhs
      let mut eqs := #[]
      for arg1 in args1, arg2 in args2 do
        let arg1Type ← inferType arg1
        if !(← isProp arg1Type) && arg1 != arg2 then
          if (← isDefEq arg1Type (← inferType arg2)) then
            eqs := eqs.push (← mkEq arg1 arg2)
          else
            eqs := eqs.push (← mkHEq arg1 arg2)
      if let some andEqs ← mkAnd? eqs then
        let result ←
          if useEq then
            mkEq eq andEqs
          else
            mkArrow eq andEqs
        mkForallFVars params (← mkForallFVars args1 (← mkForallFVars args2New result))
      else
        return none
    let rec mkArgs2 (i : Nat) (type : Expr) (args2 args2New : Array Expr) : MetaM (Option Expr) := do
      if h : i < args1.size then
        match (← whnf type) with
        | Expr.forallE n d b _ =>
          let arg1 := args1.get ⟨i, h⟩
          if arg1.occurs resultType then
            mkArgs2 (i + 1) (b.instantiate1 arg1) (args2.push arg1) args2New
          else
            withLocalDecl n (if useEq then BinderInfo.default else BinderInfo.implicit) d fun arg2 =>
              mkArgs2 (i + 1) (b.instantiate1 arg2) (args2.push arg2) (args2New.push arg2)
        | _ => throwError "unexpected constructor type for '{ctorVal.name}'"
      else
        jp args2 args2New
    if useEq then
      mkArgs2 0 type #[] #[]
    else
      withNewBinderInfos (params.map fun param => (param.fvarId!, BinderInfo.implicit)) <|
      withNewBinderInfos (args1.map fun arg1 => (arg1.fvarId!, BinderInfo.implicit)) <|
        mkArgs2 0 type #[] #[]

private def mkInjectiveTheoremType? (ctorVal : ConstructorVal) : MetaM (Option Expr) :=
  mkInjectiveTheoremTypeCore? ctorVal false

private def injTheoremFailureHeader (ctorName : Name) : MessageData :=
  m!"failed to prove injectivity theorem for constructor '{ctorName}', use 'set_option genInjectivity false' to disable the generation"

private def throwInjectiveTheoremFailure {α} (ctorName : Name) (mvarId : MVarId) : MetaM α :=
  throwError "{injTheoremFailureHeader ctorName}{indentD <| MessageData.ofGoal mvarId}"

private def solveEqOfCtorEq (ctorName : Name) (mvarId : MVarId) (h : FVarId) : MetaM Unit := do
  match (← injection mvarId h) with
  | InjectionResult.solved => unreachable!
  | InjectionResult.subgoal mvarId .. =>
    (← splitAnd mvarId).forM fun mvarId =>
      unless (← assumptionCore mvarId) do
        throwInjectiveTheoremFailure ctorName mvarId

private def mkInjectiveTheoremValue (ctorName : Name) (targetType : Expr) : MetaM Expr :=
  forallTelescopeReducing targetType fun xs type => do
    let mvar ← mkFreshExprSyntheticOpaqueMVar type
    solveEqOfCtorEq ctorName mvar.mvarId! xs.back.fvarId!
    mkLambdaFVars xs mvar

def mkInjectiveTheoremNameFor (ctorName : Name) : Name :=
  ctorName ++ `inj

private def mkInjectiveTheorem (ctorVal : ConstructorVal) : MetaM Unit := do
  let some type ← mkInjectiveTheoremType? ctorVal
    | return ()
  let value ← mkInjectiveTheoremValue ctorVal.name type
  addDecl <| Declaration.thmDecl {
    name        := mkInjectiveTheoremNameFor ctorVal.name
    levelParams := ctorVal.levelParams
    type        := (← instantiateMVars type)
    value       := (← instantiateMVars value)
  }

def mkInjectiveEqTheoremNameFor (ctorName : Name) : Name :=
  ctorName ++ `injEq

private def mkInjectiveEqTheoremType? (ctorVal : ConstructorVal) : MetaM (Option Expr) :=
  mkInjectiveTheoremTypeCore? ctorVal true

private def mkInjectiveEqTheoremValue (ctorName : Name) (targetType : Expr) : MetaM Expr := do
  forallTelescopeReducing targetType fun xs type => do
    let mvar ← mkFreshExprSyntheticOpaqueMVar type
    let [mvarId₁, mvarId₂] ← apply mvar.mvarId! (mkConst ``Eq.propIntro)
      | throwError "unexpected number of subgoals when proving injective theorem for constructor '{ctorName}'"
    let (h, mvarId₁) ← intro1 mvarId₁
    let (_, mvarId₂) ← intro1 mvarId₂
    solveEqOfCtorEq ctorName mvarId₁ h
    let mvarId₂ ← casesAnd mvarId₂
    let mvarId₂ ← substEqs mvarId₂
    applyRefl mvarId₂ (injTheoremFailureHeader ctorName)
    mkLambdaFVars xs mvar

private def mkInjectiveEqTheorem (ctorVal : ConstructorVal) : MetaM Unit := do
  let some type ← mkInjectiveEqTheoremType? ctorVal
    | return ()
  let value ← mkInjectiveEqTheoremValue ctorVal.name type
  let name := mkInjectiveEqTheoremNameFor ctorVal.name
  addDecl <| Declaration.thmDecl {
    name
    levelParams := ctorVal.levelParams
    type        := (← instantiateMVars type)
    value       := (← instantiateMVars value)
  }
  addSimpLemma (ext := simpExtension) name (post := true) (inv := false) AttributeKind.global (prio := eval_prio default)

register_builtin_option genInjectivity : Bool := {
  defValue := true
  descr    := "generate injectivity theorems for inductive datatype constructors"
}

def mkInjectiveTheorems (declName : Name) : MetaM Unit := do
  if (← getEnv).contains ``Eq.propIntro && genInjectivity.get (← getOptions) &&  !(← isInductivePredicate declName) then
    let info ← getConstInfoInduct declName
    unless info.isUnsafe do
      for ctor in info.ctors do
        let ctorVal ← getConstInfoCtor ctor
        if ctorVal.numFields > 0 then
          mkInjectiveTheorem ctorVal
          mkInjectiveEqTheorem ctorVal

end Lean.Meta
