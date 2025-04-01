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
  /-- Overrides to param binders to apply after param binder info inference. -/
  paramInfoOverrides : List (Option BinderInfo) := []

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
          let {ref, projName, paramInfoOverrides} := projDecls[i]
          unless ctorType.isForall do
            throwErrorAt ref "\
              failed to generate projection '{projName}' for '{.ofConstName n}', \
              not enough constructor fields"
          unless paramInfoOverrides.length ≤ params.size do
            throwErrorAt ref "\
              failed to generate projection '{projName}' for '{.ofConstName n}', \
              too many structure parameter overrides"
          let resultType := ctorType.bindingDomain!.consumeTypeAnnotations
          let isProp ← isProp resultType
          if isPredicate && !isProp then
            throwErrorAt ref "\
              failed to generate projection '{projName}' for the 'Prop'-valued type '{.ofConstName n}', \
              field must be a proof, but it has type\
              {indentExpr resultType}"
          let projType := lctx.mkForall projArgs resultType
          let projType := projType.inferImplicit indVal.numParams (considerRange := true)
          let projType := projType.updateForallBinderInfos paramInfoOverrides
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

/--
Checks if the expression is of the form `S.mk x.1 ... x.n` with `n` nonzero
and `S.mk` a structure constructor with `S` one of the recorded structure parents.
Returns `x`.
Each projection `x.i` can be either a native projection or from a projection function.
-/
def etaStruct? (e : Expr) (p : Name → Bool) : MetaM (Option Expr) := do
  let .const ctor _ := e.getAppFn | return none
  let some (ConstantInfo.ctorInfo fVal) := (← getEnv).find? ctor | return none
  unless p fVal.induct do return none
  unless 0 < fVal.numFields && e.getAppNumArgs == fVal.numParams + fVal.numFields do return none
  let args := e.getAppArgs
  let params := args.extract 0 fVal.numParams
  let some x ← getProjectedExpr ctor fVal.induct params 0 args[fVal.numParams]! none | return none
  for i in [1 : fVal.numFields] do
    let arg := args[fVal.numParams + i]!
    let some x' ← getProjectedExpr ctor fVal.induct params i arg x | return none
    unless x' == x do return none
  return x
where
  sameParams (params1 params2 : Array Expr) : MetaM Bool := withNewMCtxDepth do
    if params1.size == params2.size then
      for p1 in params1, p2 in params2 do
        unless ← isDefEqGuarded p1 p2 do
          return false
      return true
    else
      return false
  /--
  Given an expression `e` that's either a native projection or a registered projection
  function, gives the object being projected.
  Checks that the parameters are defeq to `params`, that the projection index is equal to `idx`,
  and, if `x?` is provided, that the object being projected is equal to it.
  -/
  getProjectedExpr (ctor induct : Name) (params : Array Expr) (idx : Nat) (e : Expr) (x? : Option Expr) : MetaM (Option Expr) := do
    if let .proj S i x := e then
      if i == idx && induct == S && (x? |>.map (· == x) |>.getD true) then
        let ety ← whnf (← inferType e)
        let params' := ety.getAppArgs
        if ← sameParams params params' then
          return x
      return none
    if let .const fn _ := e.getAppFn then
      if let some info ← getProjectionFnInfo? fn then
        if info.ctorName == ctor && info.i == idx && e.getAppNumArgs == info.numParams + 1 then
          let x := e.appArg!
          if (x? |>.map (· == x) |>.getD true) then
            let params' := e.appFn!.getAppArgs
            if ← sameParams params params' then
              return e.appArg!
    return none

/--
Eta reduces all structures satisfying `p` in the whole expression.

See `etaStruct?` for reducing single expressions.
-/
def etaStructReduce (e : Expr) (p : Name → Bool) : MetaM Expr := do
  let e ← instantiateMVars e
  Meta.transform e (post := fun e => do
    if let some e ← etaStruct? e p then
      return .done e
    else
      return .continue)

/--
Instantiates the default value given by the default value function `defaultFn`.
- `defaultFn` is the default value function returned by `Lean.getEffectiveDefaultFnForField?` or `Lean.getDefaultFnForField?`.
- `levels?` is the list of levels to use, and otherwise the levels are inferred.
- `params` is the list of structure parameters. These are assumed to be correct for the given levels.
- `fieldVal?` is a function for getting fields for values, if they exist.

If successful, returns a set of fields used and the resulting default value.
Success is expected. Callers should do metacontext backtracking themselves if needed.
-/
partial def instantiateStructDefaultValueFn?
    [Monad m] [MonadEnv m] [MonadError m] [MonadLiftT MetaM m] [MonadControlT MetaM m]
    (defaultFn : Name) (levels? : Option (List Level)) (params : Array Expr)
    (fieldVal? : Name → m (Option Expr)) : m (Option (NameSet × Expr)) := do
  let cinfo ← getConstInfo defaultFn
  let us ← levels?.getDM (mkFreshLevelMVarsFor cinfo)
  assert! us.length == cinfo.levelParams.length
  let mut val ← liftMetaM <| instantiateValueLevelParams cinfo us
  for param in params do
    let .lam _ t b _ := val | return none
    -- If no levels given, need to unify to solve for level mvars.
    if levels?.isNone then
      unless (← isDefEq (← inferType param) t) do return none
    val := b.instantiate1 param
  go? {} val
where
  go? (usedFields : NameSet) (e : Expr) : m (Option (NameSet × Expr)) := do
    match e with
    | .lam n d b _ =>
      let some val ← fieldVal? n | return none
      if (← isDefEq (← inferType val) d) then
        go? (usedFields.insert n) (b.instantiate1 val)
      else
        return none
    | e =>
      let_expr id _ a := e | return some (usedFields, e)
      return some (usedFields, a)

end Lean.Meta
