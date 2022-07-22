/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.AuxRecursor
import Lean.Meta.AppBuilder

namespace Lean

@[extern "lean_mk_cases_on"] opaque mkCasesOnImp (maxHeartbeats: Nat) (env : Environment) (declName : @& Name) : Except KernelException Environment
@[extern "lean_mk_rec_on"] opaque mkRecOnImp (maxHeartbeats: Nat) (env : Environment) (declName : @& Name) : Except KernelException Environment
@[extern "lean_mk_no_confusion"] opaque mkNoConfusionCoreImp (maxHeartbeats: Nat) (env : Environment) (declName : @& Name) : Except KernelException Environment
@[extern "lean_mk_below"] opaque mkBelowImp (maxHeartbeats: Nat) (env : Environment) (declName : @& Name) : Except KernelException Environment
@[extern "lean_mk_ibelow"] opaque mkIBelowImp (maxHeartbeats: Nat) (env : Environment) (declName : @& Name) : Except KernelException Environment
@[extern "lean_mk_brec_on"] opaque mkBRecOnImp (maxHeartbeats: Nat) (env : Environment) (declName : @& Name) : Except KernelException Environment
@[extern "lean_mk_binduction_on"] opaque mkBInductionOnImp (maxHeartbeats: Nat) (env : Environment) (declName : @& Name) : Except KernelException Environment

variable [Monad m] [MonadEnv m] [MonadError m] [MonadOptions m]

@[inline] private def adaptFn (f : Nat → Environment → Name → Except KernelException Environment) (maxHeartbeats: Nat) (declName : Name) : m Unit := do
  match f maxHeartbeats (← getEnv) declName with
  | Except.ok env   => modifyEnv fun _ => env
  | Except.error ex => throwKernelException ex

def mkCasesOn (maxHeartbeats: Nat) (declName : Name) : m Unit := adaptFn mkCasesOnImp maxHeartbeats declName 
def mkRecOn (maxHeartbeats: Nat)  (declName : Name) : m Unit := adaptFn mkRecOnImp maxHeartbeats declName 
def mkNoConfusionCore (maxHeartbeats: Nat) (declName : Name) : m Unit := adaptFn mkNoConfusionCoreImp maxHeartbeats declName 
def mkBelow (maxHeartbeats: Nat) (declName : Name) : m Unit := adaptFn mkBelowImp maxHeartbeats declName 
def mkIBelow (maxHeartbeats: Nat) (declName : Name) : m Unit := adaptFn mkIBelowImp maxHeartbeats declName 
def mkBRecOn (maxHeartbeats: Nat) (declName : Name) : m Unit := adaptFn mkBRecOnImp maxHeartbeats declName 
def mkBInductionOn (maxHeartbeats: Nat) (declName : Name) : m Unit := adaptFn mkBInductionOnImp maxHeartbeats declName 

open Meta

def mkNoConfusionEnum (enumName : Name) : MetaM Unit := do
  if (← getEnv).contains ``noConfusionEnum then
    mkToCtorIdx
    mkNoConfusionType
    mkNoConfusion
  else
    mkNoConfusionCore (← Core.getMaxHeartbeats) enumName
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
      addAndCompile (← Core.getMaxHeartbeats)  <| Declaration.defnDecl {
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
      addAndCompile (← Core.getMaxHeartbeats) <| Declaration.defnDecl {
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
      addAndCompile (← Core.getMaxHeartbeats) <| Declaration.defnDecl {
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
    mkNoConfusionCore (← Core.getMaxHeartbeats) declName

end Lean
