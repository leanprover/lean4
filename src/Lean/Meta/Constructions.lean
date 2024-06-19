/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.AuxRecursor
import Lean.AddDecl
import Lean.Meta.AppBuilder
import Lean.Meta.CompletionName

namespace Lean

@[extern "lean_mk_rec_on"] opaque mkRecOnImp (env : Environment) (declName : @& Name) : Except KernelException Declaration
@[extern "lean_mk_cases_on"] opaque mkCasesOnImp (env : Environment) (declName : @& Name) : Except KernelException Declaration
@[extern "lean_mk_no_confusion_type"] opaque mkNoConfusionTypeCoreImp (env : Environment) (declName : @& Name) : Except KernelException Declaration
@[extern "lean_mk_no_confusion"] opaque mkNoConfusionCoreImp (env : Environment) (declName : @& Name) : Except KernelException Declaration
@[extern "lean_mk_below"] opaque mkBelowImp (env : Environment) (declName : @& Name) (ibelow : Bool) : Except KernelException Declaration
@[extern "lean_mk_brec_on"] opaque mkBRecOnImp (env : Environment) (declName : @& Name) (ind : Bool) : Except KernelException Declaration

open Meta

def mkRecOn (declName : Name) : MetaM Unit := do
  let name := mkRecOnName declName
  let decl ← ofExceptKernelException (mkRecOnImp (← getEnv) declName)
  addDecl decl
  setReducibleAttribute name
  modifyEnv fun env => markAuxRecursor env name
  modifyEnv fun env => addProtected env name

def mkCasesOn (declName : Name) : MetaM Unit := do
  let name := mkCasesOnName declName
  let decl ← ofExceptKernelException (mkCasesOnImp (← getEnv) declName)
  addDecl decl
  setReducibleAttribute name
  modifyEnv fun env => markAuxRecursor env name
  modifyEnv fun env => addProtected env name

private def mkBelowOrIBelow (declName : Name) (ibelow : Bool) : MetaM Unit := do
  let .inductInfo indVal ← getConstInfo declName | return
  unless indVal.isRec do return
  if ← isPropFormerType indVal.type then return

  let decl ← ofExceptKernelException (mkBelowImp (← getEnv) declName ibelow)
  let name := decl.definitionVal!.name
  addDecl decl
  setReducibleAttribute name
  modifyEnv fun env => addToCompletionBlackList env name
  modifyEnv fun env => addProtected env name

def mkBelow (declName : Name) : MetaM Unit := mkBelowOrIBelow declName true
def mkIBelow (declName : Name) : MetaM Unit := mkBelowOrIBelow declName false

private def mkBRecOrBInductionOn (declName : Name) (ind : Bool) : MetaM Unit := do
  let .inductInfo indVal ← getConstInfo declName | return
  unless indVal.isRec do return
  if ← isPropFormerType indVal.type then return
  let .recInfo recInfo ← getConstInfo (mkRecName declName) | return
  unless recInfo.numMotives = indVal.all.length do
    /-
    The mutual declaration containing `declName` contains nested inductive datatypes.
    We don't support this kind of declaration here yet. We probably never will :)
    To support it, we will need to generate an auxiliary `below` for each nested inductive
    type since their default `below` is not good here. For example, at
    ```
    inductive Term
    | var : String -> Term
    | app : String -> List Term -> Term
    ```
    The `List.below` is not useful since it will not allow us to recurse over the nested terms.
    We need to generate another one using the auxiliary recursor `Term.rec_1` for `List Term`.
    -/
    return

  let decl ← ofExceptKernelException (mkBRecOnImp (← getEnv) declName ind)
  let name := decl.definitionVal!.name
  addDecl decl
  setReducibleAttribute name
  modifyEnv fun env => markAuxRecursor env name
  modifyEnv fun env => addProtected env name

def mkBRecOn (declName : Name) : MetaM Unit := mkBRecOrBInductionOn declName false
def mkBInductionOn (declName : Name) : MetaM Unit := mkBRecOrBInductionOn declName true

def mkNoConfusionCore (declName : Name) : MetaM Unit := do
  -- Do not do anything unless can_elim_to_type. TODO: Extract to util
  let .inductInfo indVal ← getConstInfo declName | return
  let recInfo ← getConstInfo (mkRecName declName)
  unless recInfo.levelParams.length > indVal.levelParams.length do return

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

def mkNoConfusionEnum (enumName : Name) : MetaM Unit := do
  if (← getEnv).contains ``noConfusionEnum then
    mkToCtorIdx
    mkNoConfusionType
    mkNoConfusion
  else
    -- `noConfusionEnum` was not defined yet, so we use `mkNoConfusionCore`
    mkNoConfusionCore enumName
where

  mkToCtorIdx : MetaM Unit := do
    let ConstantInfo.inductInfo info ← getConstInfo enumName | unreachable!
    let us := info.levelParams.map mkLevelParam
    let numCtors := info.ctors.length
    let declName := Name.mkStr enumName "toCtorIdx"
    let enumType := mkConst enumName us
    let natType  := mkConst ``Nat
    let declType ← mkArrow enumType natType
    let mut minors := #[]
    for i in [:numCtors] do
      minors := minors.push <| mkNatLit i
    withLocalDeclD `x enumType fun x => do
      let motive ← mkLambdaFVars #[x] natType
      let declValue ← mkLambdaFVars #[x] <| mkAppN (mkApp2 (mkConst (mkCasesOnName enumName) (levelOne::us)) motive x) minors
      addAndCompile <| Declaration.defnDecl {
        name        := declName
        levelParams := info.levelParams
        type        := declType
        value       := declValue
        safety      := DefinitionSafety.safe
        hints       := ReducibilityHints.abbrev
      }
      setReducibleAttribute declName

  mkNoConfusionType : MetaM Unit := do
    let ConstantInfo.inductInfo info ← getConstInfo enumName | unreachable!
    let us := info.levelParams.map mkLevelParam
    let v ← mkFreshUserName `v
    let enumType := mkConst enumName us
    let sortV := mkSort (mkLevelParam v)
    let toCtorIdx := mkConst (Name.mkStr enumName "toCtorIdx") us
    withLocalDeclD `P sortV fun P =>
    withLocalDeclD `x enumType fun x =>
    withLocalDeclD `y enumType fun y => do
      let declType  ← mkForallFVars #[P, x, y] sortV
      let declValue ← mkLambdaFVars #[P, x, y] (← mkAppM ``noConfusionTypeEnum #[toCtorIdx, P, x, y])
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
    let toCtorIdx := mkConst (Name.mkStr enumName "toCtorIdx") us
    let noConfusionType := mkConst (Name.mkStr enumName "noConfusionType") (mkLevelParam v :: us)
    withLocalDecl `P BinderInfo.implicit sortV fun P =>
    withLocalDecl `x BinderInfo.implicit enumType fun x =>
    withLocalDecl `y BinderInfo.implicit enumType fun y => do
    withLocalDeclD `h (← mkEq x y) fun h => do
      let declType  ← mkForallFVars #[P, x, y, h] (mkApp3 noConfusionType P x y)
      let declValue ← mkLambdaFVars #[P, x, y, h] (← mkAppOptM ``noConfusionEnum #[none, none, none, toCtorIdx, P, x, y, h])
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
  if (← isEnumType declName) then
    mkNoConfusionEnum declName
  else
    mkNoConfusionCore declName

end Lean
