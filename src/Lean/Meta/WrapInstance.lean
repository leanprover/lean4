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
   return `i`; otherwise wrap it in an auxiliary definition of type `I'` and return it
   (controlled by `backward.inferInstanceAs.wrap.instances`).
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

/--
Rebuild a type application with fresh synthetic metavariables for instance-implicit arguments.
Non-instance-implicit arguments are assigned from the original application's arguments.
If the function is over-applied, extra arguments are preserved.
-/
public def abstractInstImplicitArgs (type : Expr) : MetaM Expr := do
  let fn := type.getAppFn
  let args := type.getAppArgs
  let (mvars, bis, _) ← forallMetaTelescope (← inferType fn)
  for i in [:mvars.size] do
    unless bis[i]!.isInstImplicit do
      mvars[i]!.mvarId!.assign args[i]!
  let args := mvars ++ args.drop mvars.size
  instantiateMVars (mkAppN fn args)

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

/--
Wrap an instance value so its type matches the expected type exactly.
See the module docstring for the full algorithm specification.
-/
public partial def wrapInstance (inst expectedType : Expr) (compile : Bool := true)
    (logCompileErrors : Bool := true) (isMeta : Bool := false) : MetaM Expr := withTransparency .instances do
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

  -- Try to reduce it to a constructor.
  (← whnf inst).withApp fun f args => do
    let some (.ctorInfo ci) ← f.constName?.mapM getConstInfo
      | do
        trace[Meta.wrapInstance] "did not reduce to constructor application, returning/wrapping as is: {inst}"
        if backward.inferInstanceAs.wrap.instances.get (← getOptions) then
          let instType ← inferType inst
          if ← isDefEq expectedType instType then
            return inst
          else
            let name ← mkAuxDeclName
            let wrapped ← mkAuxDefinition name expectedType inst (compile := false)
            setReducibilityStatus name .implicitReducible
            if isMeta then modifyEnv (markMeta · name)
            if compile then
              compileDecls (logErrors := logCompileErrors) #[name]
            enableRealizationsForConst name
            return wrapped
        else
          return inst
    let (mvars, _, cls) ← forallMetaTelescope (← inferType f)
    if h₁ : args.size ≠ mvars.size then
      throwError "wrapInstance: incorrect number of arguments for \
        constructor application `{f}`: {args}"
    else
      unless ← isDefEq expectedType cls do
        throwError "wrapInstance: `{expectedType}` does not unify with the conclusion of \
          `{.ofConstName ci.name}`"
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
                trace[Meta.wrapInstance] "using existing instance {new}"
                mvarId.assign new
                continue
            catch _ => pure ()

          mvarId.assign (← wrapInstance arg argExpectedType (compile := compile)
            (logCompileErrors := logCompileErrors) (isMeta := isMeta))
          continue

        if backward.inferInstanceAs.wrap.reuseSubInstances.get (← getOptions) then
          let (baseClassName, fieldInfo) ← getFieldOrigin className mvarDecl.userName
          if baseClassName != className then
            trace[Meta.wrapInstance] "found inherited field `{mvarDecl.userName}` from parent `{baseClassName}`"
            if let some baseClassType ← getParentStructType? className baseClassName expectedType then
              try
                if let .some existingBaseClassInst ← trySynthInstance baseClassType then
                  trace[Meta.wrapInstance] "using projection of existing instance `{existingBaseClassInst}`"
                  mvarId.assign (← mkProjection existingBaseClassInst fieldInfo.fieldName)
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
