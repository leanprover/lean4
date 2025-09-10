/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.AddDecl
public import Lean.Meta.AppBuilder
public import Lean.Meta.CompletionName
public import Lean.Meta.Constructions.NoConfusionLinear
import Lean.Meta.Constructions.CtorIdx

public section

namespace Lean

@[extern "lean_mk_no_confusion_type"] opaque mkNoConfusionTypeCoreImp (env : Environment) (declName : @& Name) : Except Kernel.Exception Declaration

open Meta

def mkNoConfusionCoreImp (indName : Name) : MetaM Unit := do
  let declName := Name.mkStr indName "noConfusion"
  let noConfusionTypeName := Name.mkStr indName "noConfusionType"
  let ConstantInfo.inductInfo info ← getConstInfo indName | unreachable!
  let casesOnName := mkCasesOnName indName
  let casesOnInfo ← getConstVal casesOnName
  let v::us := casesOnInfo.levelParams.map mkLevelParam | panic! "unexpected universe levels on `casesOn`"
  let e ← forallBoundedTelescope (← inferType (mkConst noConfusionTypeName (v::us))) (info.numParams + info.numIndices) fun xs _ => do
    let params : Array Expr := xs[:info.numParams]
    let is : Array Expr := xs[info.numParams:]
    let PType := mkSort v
    withLocalDecl `P .implicit PType fun P =>
    withLocalDecl `x1 .implicit (mkAppN (mkConst indName us) xs) fun x1 =>
    withLocalDecl `x2 .implicit (mkAppN (mkConst indName us) xs) fun x2 => do
    withLocalDeclD `h12 (← mkEq x1 x2) fun h12 => do
      let target1 := mkAppN (mkConst noConfusionTypeName (v :: us)) (xs ++ #[P, x1, x1])
      let motive1 ← mkLambdaFVars (is ++ #[x1]) target1
      let e ← withLocalDeclD `h11 (← mkEq x1 x1) fun h11 => do
        let alts ← info.ctors.mapM fun ctor => do
          let ctorType ← inferType (mkAppN (mkConst ctor us) params)
          forallTelescopeReducing ctorType fun fs _ => do
            let kType := (← mkNoConfusionCtorArg ctor P).beta (params ++ fs ++ fs)
            withLocalDeclD `k kType fun k => do
              let mut e := k
              let eqns ← arrowDomainsN kType.getNumHeadForalls kType
              for eqn in eqns do
                if let some (_, x, _) := eqn.eq? then
                  e := mkApp e (← mkEqRefl x)
                else if let some (_, x, _, _) := eqn.heq? then
                  e := mkApp e (← mkHEqRefl x)
                else
                  throwError "unexpected equation {eqn} in `mkNoConfusionCtorArg` for {ctor}"
              mkLambdaFVars (fs ++ #[k]) e
        let e := mkAppN (mkConst casesOnName (v :: us)) (params ++ #[motive1] ++ is ++ #[x1] ++ alts)
        mkLambdaFVars #[h11] e
      let target2 := mkAppN (mkConst noConfusionTypeName (v :: us)) (xs ++ #[P, x1, x2])
      let motive2 ← mkLambdaFVars #[x2] (← mkArrow (← mkEq x1 x2) target2)
      let e ← mkEqNDRec motive2 e h12
      let e := mkApp e h12
      mkLambdaFVars (xs ++ #[P, x1, x2, h12]) e

  addDecl (.defnDecl (← mkDefinitionValInferringUnsafe
    (name        := declName)
    (levelParams := casesOnInfo.levelParams)
    (type        := (← inferType e))
    (value       := e)
    (hints       := ReducibilityHints.abbrev)))
  setReducibleAttribute declName
  modifyEnv fun env => markNoConfusion env declName
  modifyEnv fun env => addProtected env declName


def mkNoConfusionCore (declName : Name) : MetaM Unit := do
  -- Do not do anything unless can_elim_to_type. TODO: Extract to util
  let .inductInfo indVal ← getConstInfo declName | return
  let recInfo ← getConstInfo (mkRecName declName)
  unless recInfo.levelParams.length > indVal.levelParams.length do return
  if (← isPropFormerType indVal.type) then return

  let useLinear ← NoConfusionLinear.canUse declName

  if useLinear then
    NoConfusionLinear.mkNoConfusionTypeLinear declName
  else
    let name := Name.mkStr declName "noConfusionType"
    let decl ← ofExceptKernelException (mkNoConfusionTypeCoreImp (← getEnv) declName)
    addDecl decl
    setReducibleAttribute name
    modifyEnv fun env => addToCompletionBlackList env name
    modifyEnv fun env => addProtected env name

  mkNoConfusionCoreImp declName


def mkNoConfusionEnum (enumName : Name) : MetaM Unit := do
  if (← getEnv).contains ``noConfusionEnum then
    mkNoConfusionType
    mkNoConfusion
  else
    -- `noConfusionEnum` was not defined yet, so we use `mkNoConfusionCore`
    mkNoConfusionCore enumName
where
  mkNoConfusionType : MetaM Unit := do
    let ConstantInfo.inductInfo info ← getConstInfo enumName | unreachable!
    let us := info.levelParams.map mkLevelParam
    let v ← mkFreshUserName `v
    let enumType := mkConst enumName us
    let sortV := mkSort (mkLevelParam v)
    withLocalDeclD `P sortV fun P =>
    withLocalDeclD `x enumType fun x =>
    withLocalDeclD `y enumType fun y => do
      let declType  ← mkForallFVars #[P, x, y] sortV
      let declValue ←
        if info.numCtors = 1 then
          mkLambdaFVars #[P, x, y] (← mkArrow P P)
        else
          let ctorIdx := mkConst (mkCtorIdxName enumName) us
          mkLambdaFVars #[P, x, y] (← mkAppM ``noConfusionTypeEnum #[ctorIdx, P, x, y])
      let declName  := Name.mkStr enumName "noConfusionType"
      addAndCompile <| Declaration.defnDecl {
        name        := declName
        levelParams := v :: info.levelParams
        type        := declType
        value       := declValue
        safety      := DefinitionSafety.safe
        hints       := ReducibilityHints.abbrev
      }
      setReducibleAttribute declName

  mkNoConfusion : MetaM Unit := do
    let ConstantInfo.inductInfo info ← getConstInfo enumName | unreachable!
    let us := info.levelParams.map mkLevelParam
    let v ← mkFreshUserName `v
    let enumType := mkConst enumName us
    let sortV := mkSort (mkLevelParam v)
    let ctorIdx := mkConst (mkCtorIdxName enumName) us
    let noConfusionType := mkConst (Name.mkStr enumName "noConfusionType") (mkLevelParam v :: us)
    withLocalDecl `P BinderInfo.implicit sortV fun P =>
    withLocalDecl `x BinderInfo.implicit enumType fun x =>
    withLocalDecl `y BinderInfo.implicit enumType fun y => do
    withLocalDeclD `h (← mkEq x y) fun h => do
      let declType  ← mkForallFVars #[P, x, y, h] (mkApp3 noConfusionType P x y)
      let declValue ← mkLambdaFVars #[P, x, y, h] <| ← do
        if info.numCtors = 1 then
          withLocalDeclD `p P fun p => mkLambdaFVars #[p] p
        else
          mkAppOptM ``noConfusionEnum #[none, none, none, ctorIdx, P, x, y, h]
      let declName  := Name.mkStr enumName "noConfusion"
      addAndCompile <| Declaration.defnDecl {
        name        := declName
        levelParams := v :: info.levelParams
        type        := declType
        value       := declValue
        safety      := DefinitionSafety.safe
        hints       := ReducibilityHints.abbrev
      }
      setReducibleAttribute declName
      modifyEnv fun env => markNoConfusion env declName

def mkNoConfusion (declName : Name) : MetaM Unit := do
  withTraceNode `Meta.mkNoConfusion (fun _ => return m!"{declName}") do
  if (← isEnumType declName) then
    mkNoConfusionEnum declName
  else
    mkNoConfusionCore declName

builtin_initialize
  registerTraceClass `Meta.mkNoConfusion

end Lean
