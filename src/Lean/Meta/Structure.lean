/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Kyle Miller
-/
prelude
import Lean.AddDecl
import Lean.Structure
import Lean.Meta.AppBuilder

/-!
# Structure methods that require `MetaM` infrastructure
-/

namespace Lean.Meta

/--
If `struct` is an application of the form `S ..` with `S` a constant for a structure,
returns the name of the structure, otherwise throws an error.
-/
def getStructureName (struct : Expr) : MetaM Name :=
  match struct.getAppFn with
  | Expr.const declName .. => do
    unless isStructure (← getEnv) declName do
      throwError "'{declName}' is not a structure"
    return declName
  | _ => throwError "expected structure"

/--
Structure projection declaration for `mkProjections`.
-/
structure StructProjDecl where
  ref : Syntax
  projName : Name

/--
Adds projection functions to the environment for the one-constructor inductive type named `n`.
- The `projName`s in each `StructProjDecl` are used for the names of the declarations added to the environment.
- If `instImplicit` is true, then generates projections with `self` being instance implicit.

Notes:
- This function supports everything that `Expr.proj` supports (see `lean::type_checker::infer_proj`).
  This means we can generate projections for inductive types with one-constructor,
  even if it is an indexed family (which is not supported by the `structure` command).
- We throw errors in the cases that `Expr.proj` is not type-correct.
-/
def mkProjections (n : Name) (projDecls : Array StructProjDecl) (instImplicit : Bool) : MetaM Unit :=
  withLCtx {} {} do
    let indVal ← getConstInfoInduct n
    if indVal.numCtors != 1 then
      throwError "cannot generate projections for '{.ofConstName n}', does not have exactly one constructor"
    let ctorVal ← getConstInfoCtor indVal.ctors.head!
    let isPredicate ← isPropFormerType indVal.type
    let lvls := indVal.levelParams.map mkLevelParam
    forallBoundedTelescope ctorVal.type indVal.numParams fun params ctorType => do
      if params.size != indVal.numParams then
        throwError "projection generation failed, '{.ofConstName n}' is an ill-formed inductive datatype"
      let selfType := mkAppN (.const n lvls) params
      let selfBI : BinderInfo := if instImplicit then .instImplicit else .default
      withLocalDecl `self selfBI selfType fun self => do
        let projArgs := params.push self
        -- Make modifications to parameter binder infos that apply to all projections
        let mut lctx ← getLCtx
        for param in params do
          let fvarId := param.fvarId!
          let decl ← fvarId.getDecl
          if !decl.binderInfo.isInstImplicit && !decl.type.isOutParam then
            /- We reset the implicit binder to have it be inferred by `Expr.inferImplicit`.
               However, outparams must be implicit. -/
            lctx := lctx.setBinderInfo fvarId .default
          else if decl.binderInfo.isInstImplicit && instImplicit then
            lctx := lctx.setBinderInfo fvarId .implicit
        -- Construct the projection functions:
        let mut ctorType := ctorType
        for h : i in [0:projDecls.size] do
          let {ref, projName} := projDecls[i]
          unless ctorType.isForall do
            throwErrorAt ref "\
              failed to generate projection '{projName}' for '{.ofConstName n}', \
              not enough constructor fields"
          let resultType := ctorType.bindingDomain!.consumeTypeAnnotations
          let isProp ← isProp resultType
          if isPredicate && !isProp then
            throwErrorAt ref "\
              failed to generate projection '{projName}' for the 'Prop'-valued type '{.ofConstName n}', \
              field must be a proof, but it has type\
              {indentExpr resultType}"
          let projType := lctx.mkForall projArgs resultType
          let projType := projType.inferImplicit indVal.numParams (considerRange := true)
          let projVal := lctx.mkLambda projArgs <| Expr.proj n i self
          let cval : ConstantVal := { name := projName, levelParams := indVal.levelParams, type := projType }
          withRef ref do
            if isProp then
              let env ← getEnv
              addDecl <|
                if env.hasUnsafe projType || env.hasUnsafe projVal then
                  -- Theorems cannot be unsafe, using opaque instead.
                  Declaration.opaqueDecl { cval with value := projVal, isUnsafe := true }
                else
                  Declaration.thmDecl { cval with value := projVal }
            else
              let decl ← mkDefinitionValInferrringUnsafe projName indVal.levelParams projType projVal ReducibilityHints.abbrev
              -- Projections have special compiler support. No need to compile.
              addDecl <| Declaration.defnDecl decl
              -- Recall: we want instance projections to be in "reducible canonical form"
              if !instImplicit then
                setReducibleAttribute projName
          modifyEnv fun env => addProjectionFnInfo env projName ctorVal.name indVal.numParams i instImplicit
          let proj := mkApp (mkAppN (.const projName lvls) params) self
          ctorType := ctorType.bindingBody!.instantiate1 proj

end Lean.Meta
