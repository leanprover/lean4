/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Authors: Eric Wieser, Kyle Miller, Jovan Gerbscheid, Kim Morrison, Sebastian Ullrich
-/
module

prelude
public import Lean.Meta.Closure
public import Lean.Meta.SynthInstance
public import Lean.Meta.CtorRecognizer
public import Lean.Meta.AppBuilder
import Lean.Structure
import Lean.ExtraModUses

/-!
# Instance Wrapping

Both `inferInstanceAs` and the default `deriving` handler wrap instance bodies to ensure
that when deriving or inferring an instance for a semireducible type definition, the
definition's RHS is not leaked when reduced at lower than semireducible transparency.

## Algorithm

Given an instance `i : I` and expected type `I'` (where `I'` must be mvar-free),
`wrapInstance` constructs a result instance as follows, executing all steps at
`instances` transparency:

1. If `I'` is not a class application, return `i` unchanged.
2. If `I'` is a proposition, wrap `i` in an auxiliary theorem of type `I'` and return it
   (controlled by `backward.inferInstanceAs.wrap.instances`).
3. Reduce `i` to whnf.
4. If `i` is not a constructor application: if `I` is already defeq to `I'`,
   return `i`; otherwise (if `backward.inferInstanceAs.wrap.reuseSubInstances` is set) try
   (recursive) eta-expansion and wrapping of `i` to see if any sub-instances can be reused;
   otherwise wrap `i` in an auxiliary definition of type `I'` and return it (controlled by
   `backward.inferInstanceAs.wrap.instances`).
5. Otherwise, if `i` is an application of `ctor` of class `C`:
   - Unify the conclusion of the type of `ctor` with `I'` to obtain adjusted field type `Fᵢ'` for
     each field.
   - Return a new application `ctor ... : I'` where the fields are adjusted as follows:
     - If the field type is a proposition: assign directly if types are defeq, otherwise
       wrap in an auxiliary theorem.
     - If the field is a parent field (subobject) `p : P`: first try to reuse an existing
       instance that can be synthesized for `P` (controlled by
       `backward.inferInstanceAs.wrap.reuseSubInstances`) in order to preserve defeqs; if that
       fails, recurse.
     - If it is a field of a flattened parent class `C'` and
       `backward.inferInstanceAs.wrap.reuseSubInstances` is true, try synthesizing an instance of
       `C'` for `I'` and if successful, use the corresponding projection of the found instance in
       order to preserve defeqs; otherwise, continue.
       - Specifically, construct the chain of base projections from `C` to `C'` applied to `_ : I'`
         and infer its type to obtain an appropriate application of `C'` for the instance search.
     - Otherwise (non-inherited data field): assign directly if types are defeq, otherwise wrap in an
       auxiliary definition to fix the type (controlled by `backward.inferInstanceAs.wrap.data`).

## Options

- `backward.inferInstanceAs.wrap`: master switch for wrapping in both `inferInstanceAs`
  and the default `deriving` handler
- `backward.inferInstanceAs.wrap.reuseSubInstances`: reuse existing instances for sub-instance
  fields to avoid non-defeq instance diamonds
- `backward.inferInstanceAs.wrap.instances`: wrap non-reducible instances in auxiliary
  definitions
- `backward.inferInstanceAs.wrap.data`: wrap data fields in auxiliary definitions
-/

namespace Lean.Meta

public register_builtin_option backward.inferInstanceAs.wrap : Bool := {
  defValue := true
  descr := "wrap instance bodies in `inferInstanceAs` and the default `deriving` handler"
}

public register_builtin_option backward.inferInstanceAs.wrap.reuseSubInstances : Bool := {
  defValue := true
  descr := "when recursing into sub-instances, reuse existing instances for the target type instead of re-wrapping them, which can be important to avoid non-defeq instance diamonds"
}

public register_builtin_option backward.inferInstanceAs.wrap.instances : Bool := {
  defValue := true
  descr := "wrap non-reducible instances in auxiliary definitions to fix their types"
}

public register_builtin_option backward.inferInstanceAs.wrap.data : Bool := {
  defValue := true
  descr := "wrap data fields in auxiliary definitions to fix their types"
}

builtin_initialize registerTraceClass `Meta.wrapInstance

open Meta

partial def getFieldOrigin (structName field : Name) : MetaM (Name × StructureFieldInfo) := do
  let env ← getEnv
  for parent in getStructureParentInfo env structName do
    if (findField? env parent.structName field).isSome then
      return ← getFieldOrigin parent.structName field
  let some fi := getFieldInfo? env structName field
    | throwError "no such field {field} in {structName}"
  return (structName, fi)

/-- Projects application of a structure type to corresponding application of a parent structure. -/
def getParentStructType? (structName parentStructName : Name) (structType : Expr) : MetaM (Option Expr) := OptionT.run do
  let env ← getEnv
  let some path := getPathToBaseStructure? env parentStructName structName | failure
  withLocalDeclD `self structType fun self => do
    let proj ← path.foldlM (init := self) fun e projFn => do
      let ty ← whnf (← inferType e)
      let .const _ us := ty.getAppFn
        | trace[Meta.wrapInstance] "could not reduce type `{ty}`"
          failure
      let params := ty.getAppArgs
      pure <| mkApp (mkAppN (.const projFn us) params) e
    let projTy ← whnf <| ← inferType proj
    if projTy.containsFVar self.fvarId! then
      trace[Meta.wrapInstance] "parent type depends on instance fields{indentExpr projTy}"
      failure
    return projTy

def etaStructExpand? (e : Expr) : MetaM (Option Expr) := OptionT.run do
  guard <| (← liftM <| isConstructorApp? e).isNone
  let eType ← instantiateMVars (← whnf (← inferType e))
  let .const inductName us := eType.getAppFn | failure
  let env ← getEnv
  guard <| isStructure env inductName
  guard <| isNonRecStructure env inductName
  guard <| !(← isProp eType)
  let iv ← getConstInfoInduct inductName
  let some ctorName := iv.ctors.head? | failure
  let ctorInfo ← getConstInfoCtor ctorName
  let params := eType.getAppArgs.shrink ctorInfo.numParams
  let structInfo? := getStructureInfo? env inductName
  let mut result := mkAppN (mkConst ctorName us) params
  for i in *...ctorInfo.numFields do
    let proj := match structInfo?.bind (·.getProjFn? i) with
      | some projFn => mkApp (mkAppN (mkConst projFn us) params) e
      | none => mkProj inductName i e
    result := mkApp result proj
  return result

/--
Wrap an instance value so its type matches the expected type exactly.
See the module docstring for the full algorithm specification.
-/
public partial def wrapInstance (inst expectedType : Expr) (compile : Bool := true)
    (logCompileErrors : Bool := true) (isMeta : Bool := false) : MetaM Expr :=
  withTransparency .instances do
    return (← go (isEta := false) inst expectedType).get!
-- If `isEta` is true, will return `none` if no sub-instance was found, i.e. eta-expansion had no
-- effect.
where go (inst expectedType : Expr) (isEta : Bool) : MetaM (Option Expr) := do
  withTraceNode `Meta.wrapInstance
      (fun _ => return m!"type: {expectedType}") do
  let some className ← isClass? expectedType
    | return inst
  trace[Meta.wrapInstance] "class is {className}"

  if ← isProp expectedType then
    if backward.inferInstanceAs.wrap.instances.get (← getOptions) then
      return (← mkAuxTheorem expectedType inst (zetaDelta := true))
    else
      return inst

  -- record inferred instance as elab dependency before `whnf` may remove it
  if let .const n .. := inst.getAppFn then
    recordExtraModUseFromDecl n isMeta

  -- Try to reduce it to a constructor.
  (← whnf inst).withApp fun f args => do
    let some (.ctorInfo ci) ← f.constName?.mapM getConstInfo
      | do
        trace[Meta.wrapInstance] "did not reduce to constructor application: {inst}"
        let instType ← inferType inst
        if ← isDefEq expectedType instType then
          return inst

        if backward.inferInstanceAs.wrap.reuseSubInstances.get (← getOptions) then
          if let some inst ← etaStructExpand? inst then
            if let some inst ← go (isEta := true) inst expectedType then
              return inst

        if backward.inferInstanceAs.wrap.instances.get (← getOptions) then
          let name ← mkAuxDeclName
          let wrapped ← mkAuxDefinition name expectedType inst (compile := false)
          if isMeta then modifyEnv (markMeta · name)
          if compile then
            compileDecls (logErrors := logCompileErrors) #[name]
          enableRealizationsForConst name
          return wrapped

        return inst
    let (mvars, _, cls) ← forallMetaTelescope (← inferType f)
    if h₁ : args.size ≠ mvars.size then
      throwError "wrapInstance: incorrect number of arguments for \
        constructor application `{f}`: {args}"
    else
      unless ← isDefEq expectedType cls do
        throwError "wrapInstance: `{expectedType}` does not unify with the conclusion of \
          `{.ofConstName ci.name}`"
      let mut isEta := isEta
      for h₂ : i in ci.numParams...args.size do
        have : i < mvars.size := by
          simp only [ne_eq, Decidable.not_not] at h₁
          rw [← h₁]
          get_elem_tactic
        let mvarId := mvars[i].mvarId!
        let mvarDecl ← mvarId.getDecl
        let argExpectedType ← instantiateMVars mvarDecl.type
        let arg := args[i]
        if ← isProp argExpectedType then
          let argType ← inferType arg
          if ← isDefEq argExpectedType argType then
            mvarId.assign arg
          else
            trace[Meta.wrapInstance] "proof field {i} does not have expected type {argExpectedType} but {argType}, wrapping in auxiliary theorem: {arg}"
            mvarId.assign (← mkAuxTheorem argExpectedType arg (zetaDelta := true))
          continue

        -- Recurse into instance arguments of the constructor
        if (← isClass? argExpectedType).isSome then
          if backward.inferInstanceAs.wrap.reuseSubInstances.get (← getOptions) then
            -- Reuse existing instance for the target type if any. This is especially important when recursing
            -- as it guarantees subinstances of overlapping instances are defeq under more than just
            -- semireducible transparency.
            try
              if let .some new ← trySynthInstance argExpectedType then
                -- ignore instances from non-defeq diamonds
                if (← withDefault <| isDefEq new arg) then
                  trace[Meta.wrapInstance] "using existing instance {new}"
                  mvarId.assign new
                  isEta := false
                  continue
            catch _ => pure ()

          -- continue eta-expansion recursively so we know whether any sub-instance was found
          if isEta then
            if let some arg ← etaStructExpand? arg then
              if let some inst ← go (isEta := true) arg argExpectedType then
                mvarId.assign inst
                isEta := false
                continue

          mvarId.assign (← go (isEta := false) arg argExpectedType).get!
          continue

        -- If we hit a data field without having found any sub-instances, we can stop early
        if isEta then
          return none

        if backward.inferInstanceAs.wrap.reuseSubInstances.get (← getOptions) then
          let (baseClassName, fieldInfo) ← getFieldOrigin className mvarDecl.userName
          if baseClassName != className then
            trace[Meta.wrapInstance] "found inherited field `{mvarDecl.userName}` from parent `{baseClassName}`"
            if let some baseClassType ← getParentStructType? className baseClassName expectedType then
              try
                if let .some existingBaseClassInst ← trySynthInstance baseClassType then
                  let proj ← mkProjection existingBaseClassInst fieldInfo.fieldName
                  -- ignore instances from non-defeq diamonds
                  if (← withDefault <| isDefEq proj arg) then
                    trace[Meta.wrapInstance] "using projection of existing instance `{existingBaseClassInst}`"
                    mvarId.assign proj
                    continue
                trace[Meta.wrapInstance] "did not find existing instance for `{baseClassName}`"
              catch e =>
                trace[Meta.wrapInstance] "error when attempting to reuse existing instance for `{baseClassName}`: {e.toMessageData}"

        -- For data fields, assign directly or wrap in aux def to fix types.
        if backward.inferInstanceAs.wrap.data.get (← getOptions) then
          let argType ← inferType arg
          if ← isDefEq argExpectedType argType then
            mvarId.assign arg
          else
            let name ← mkAuxDeclName
            mvarId.assign (← mkAuxDefinition name argExpectedType arg (compile := false))
            setInlineAttribute name
            if isMeta then modifyEnv (markMeta · name)
            if compile then
              compileDecls (logErrors := logCompileErrors) #[name]
            enableRealizationsForConst name
        else
          mvarId.assign arg
      return mkAppN f (← mvars.mapM instantiateMVars)
