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

public section

/-!
# Instance Wrapping

Both `inferInstanceAs` and the default `deriving` handler wrap instance bodies to ensure
that when deriving or inferring an instance for a semireducible type definition, the
definition's RHS is not leaked when reduced at lower than semireducible transparency.

## Algorithm

Given an instance `i : I` and expected type `I'` (where `I'` must be mvar-free),
`wrapInstance` constructs a result instance as follows, executing all steps at
`instances` transparency:

1. If `I'` is not a class, return `i` unchanged.
2. If `I'` is a proposition, wrap `i` in an auxiliary theorem of type `I'` and return it
   (controlled by `backward.inferInstanceAs.wrap.instances`).
3. Reduce `i` to whnf.
4. If `i` is not a constructor application: if the type of `i` is already defeq to `I'`,
   return `i`; otherwise wrap it in an auxiliary definition of type `I'` and return it
   (controlled by `backward.inferInstanceAs.wrap.instances`).
5. Otherwise, for `i = ctor a₁ ... aₙ` with `ctor : C ?p₁ ... ?pₙ`:
   - Unify `C ?p₁ ... ?pₙ` with `I'`.
   - Return a new application `ctor a₁' ... aₙ' : I'` where each `aᵢ'` is constructed as:
     - If the field type is a proposition: assign directly if types are defeq, otherwise
       wrap in an auxiliary theorem.
     - If the field type is a class: first try to reuse an existing synthesized instance
       for the target type (controlled by `backward.inferInstanceAs.wrap.reuseSubInstances`);
       if that fails, recurse with source instance `aᵢ` and expected type `?pᵢ`.
     - Otherwise (data field): assign directly if types are defeq, otherwise wrap in an
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

register_builtin_option backward.inferInstanceAs.wrap : Bool := {
  defValue := true
  descr := "wrap instance bodies in `inferInstanceAs` and the default `deriving` handler"
}

register_builtin_option backward.inferInstanceAs.wrap.reuseSubInstances : Bool := {
  defValue := true
  descr := "when recursing into sub-instances, reuse existing instances for the target type instead of re-wrapping them, which can be important to avoid non-defeq instance diamonds"
}

register_builtin_option backward.inferInstanceAs.wrap.instances : Bool := {
  defValue := true
  descr := "wrap non-reducible instances in auxiliary definitions to fix their types"
}

register_builtin_option backward.inferInstanceAs.wrap.data : Bool := {
  defValue := true
  descr := "wrap data fields in auxiliary definitions to fix their types"
}

builtin_initialize registerTraceClass `Meta.wrapInstance

/--
Rebuild a type application with fresh synthetic metavariables for instance-implicit arguments.
Non-instance-implicit arguments are assigned from the original application's arguments.
If the function is over-applied, extra arguments are preserved.
-/
def abstractInstImplicitArgs (type : Expr) : MetaM Expr := do
  let fn := type.getAppFn
  let args := type.getAppArgs
  let (mvars, bis, _) ← forallMetaTelescope (← inferType fn)
  for i in [:mvars.size] do
    unless bis[i]!.isInstImplicit do
      mvars[i]!.mvarId!.assign args[i]!
  let args := mvars ++ args.drop mvars.size
  instantiateMVars (mkAppN fn args)

/--
Wrap an instance value so its type matches the expected type exactly.
See the module docstring for the full algorithm specification.
-/
partial def wrapInstance (inst expectedType : Expr) (compile : Bool := true)
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
        -- Recurse into instance arguments of the constructor
        else if (← isClass? argExpectedType).isSome then
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
        else
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

end Lean.Meta
