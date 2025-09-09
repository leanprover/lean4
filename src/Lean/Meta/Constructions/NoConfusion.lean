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
import Lean.Meta.Injective
import Lean.Meta.SameCtorUtils

public section

namespace Lean

@[extern "lean_mk_no_confusion_type"] opaque mkNoConfusionTypeCoreImp (env : Environment) (declName : @& Name) : Except Kernel.Exception Declaration
@[extern "lean_mk_no_confusion"] opaque mkNoConfusionCoreImp (env : Environment) (declName : @& Name) : Except Kernel.Exception Declaration

open Meta

def mkNoConfusionCtors (declName : Name) : MetaM Unit := do
  -- Do not do anything unless can_elim_to_type.
  let .inductInfo indVal ← getConstInfo declName | return
  let recInfo ← getConstInfo (mkRecName declName)
  unless recInfo.levelParams.length > indVal.levelParams.length do return
  if (← isPropFormerType indVal.type) then return
  let noConfusionName := Name.mkStr declName "noConfusion"

  -- We take the level names from `.rec`, as that conveniently has an extra level parameter that
  -- is distinct from the ones from the inductive
  let (v::us) := recInfo.levelParams.map mkLevelParam | throwError "unexpected number of level parameters in {recInfo.name}"

  for ctor in indVal.ctors do
    let ctorInfo ← getConstInfoCtor ctor
    let e ← withLocalDeclD `P (.sort v) fun P =>
      forallBoundedTelescope ctorInfo.type ctorInfo.numParams fun xs _ => do
        let ctorApp := mkAppN (mkConst ctor us) xs
        withSharedCtorIndices ctorApp fun ys indices ctor1 ctor2 => do
          let heqType ← mkEq ctor1 ctor2
          withLocalDeclD `h heqType fun h => do
            let noConfusionApp :=
              mkAppN (mkConst noConfusionName (v :: us)) (xs ++ indices ++ #[P, ctor1, ctor2, h])
            let noConfusionType ← inferType noConfusionApp
            -- Here we do the possible expensive reduction that we want to share
            let noConfusionType ← whnfForall noConfusionType
            -- noConfusionType := (n1 = n2 → x1 → x2 → … → P) → P
            assert! noConfusionType.isForall
            let kType := noConfusionType.bindingDomain!
            simpNoConfusionAlt kType fun k' k => do
              let noConfusionApp := mkApp noConfusionApp k
              mkLambdaFVars (xs ++ #[P] ++ ys ++ #[h, k']) noConfusionApp
    let name := ctor.str "noConfusion"
    addAndCompile (.defnDecl (← mkDefinitionValInferringUnsafe
      (name        := name)
      (levelParams := recInfo.levelParams)
      (type        := (← inferType e))
      (value       := e)
      (hints       := ReducibilityHints.abbrev)
    ))
    setReducibleAttribute name
    modifyEnv fun env => markNoConfusion env name

where
  -- Given the type
  --   t := n1 = n1 → a1 ≍ a2 → x1 = x2 → … → P
  -- of a noConfusion principle, brings a free variable
  -- `k' : a1 = a2 → x1 = x2 → … → P` into scope and constructs
  -- `k := fun _ h1 h2 => k' (eq_of_heq h1) h2` : t`
  simpNoConfusionAlt {α} (t : Expr) (cont : Expr → Expr → MetaM α) : MetaM α :=
    forallTelescopeReducing t fun hyps P => do
      let mut args := #[]
      let mut kType' := P
      for hyp in hyps.reverse do
        let hypType ← inferType hyp
        if let some (α1, x1, α2, x2) := hypType.heq? then
          if (← isDefEq α1 α2) then
            if (← isDefEq x1 x2) then
              continue
            args := args.push (← mkEqOfHEq hyp)
          else
            args := args.push hyp
        else if let some (_, x1, x2) := hypType.eq? then
          if (← isDefEq x1 x2) then
            continue
          else
            args := args.push hyp
        let hypType ← inferType args.back!
        kType' := mkForall (← hyp.fvarId!.getUserName) .default hypType kType'
      args := args.reverse
      withLocalDeclD `k kType' fun k' => do
        let k ← mkLambdaFVars hyps (mkAppN k' args)
        cont k' k

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

  let name := Name.mkStr declName "noConfusion"
  let decl ← ofExceptKernelException (mkNoConfusionCoreImp (← getEnv) declName)
  addDecl decl
  setReducibleAttribute name
  modifyEnv fun env => markNoConfusion env name
  modifyEnv fun env => addProtected env name

  mkNoConfusionCtors declName


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
