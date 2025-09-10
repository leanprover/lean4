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

/--
Creates per-constructor no-confusion definitions. These specialize the general noConfusion
declaration to equalities between two applications of the same constructor, to effectively cache
the computation of `noConfusionType` for that constructor:

```
def L.cons.noConfusion.{u_1, u} : {α : Type u} → (P : Sort u_1) →
  (x : α) → (xs : L α) → (x' : α) → (xs' : L α) →
  L.cons x xs = L.cons x' xs' →
  (x = x' → xs = xs' → P) →
  P
```

These definitions are less expressive than the general `noConfusion` principle when there are
complicated indices. In particular they assume that all fields of the constructor that appear
in its type are equal already. The `mkNoConfusion` app builder falls back to the general principle
if the per-constructor one does not apply.

At some point I tried to be clever and remove hypotheses that are trivial (`n = n →`), but that
made it harder for, say, `injection` to know how often to `intro`. So we just keep them.
-/
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
    if ctorInfo.numFields > 0 then
      let e ← withLocalDeclD `P (.sort v) fun P =>
        forallBoundedTelescope ctorInfo.type ctorInfo.numParams fun xs _ => do
          let ctorApp := mkAppN (mkConst ctor us) xs
          withSharedCtorIndices ctorApp fun ys indices fields1 fields2 => do
            let ctor1 := mkAppN ctorApp fields1
            let ctor2 := mkAppN ctorApp fields2
            let heqType ← mkEq ctor1 ctor2
            withLocalDeclD `h heqType fun h => do
              -- When the kernel checks this definitios, it will perform the potentially expensive
              -- computation that `noConfusionType h` is equal to `$kType → P`
              let kType ← mkNoConfusionCtorArg ctor P
              let kType := kType.beta (xs ++ fields1 ++ fields2)
              withLocalDeclD `k kType fun k =>
                let e := mkConst noConfusionName (v :: us)
                let e := mkAppN e (xs ++ indices ++ #[P, ctor1, ctor2, h, k])
                mkLambdaFVars (xs ++ #[P] ++ ys ++ #[h, k]) e
      let name := ctor.str "noConfusion"
      addAndCompile (.defnDecl (← mkDefinitionValInferringUnsafe
        (name        := name)
        (levelParams := recInfo.levelParams)
        (type        := (← inferType e))
        (value       := e)
        (hints       := ReducibilityHints.abbrev)
      ))
      setReducibleAttribute name
      -- NB: Do not `markNoConfusion`, it is not the no-confusion principle that
      -- the compiler expects

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
