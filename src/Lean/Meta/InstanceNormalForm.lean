/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
module

prelude
public import Lean.Meta.Closure
public import Lean.Meta.SynthInstance
public import Lean.Meta.CtorRecognizer

public section

namespace Lean.Meta

register_builtin_option «instance».normalForm : Bool := {
  defValue := true
  descr := "normalize instance bodies to constructor-based normal form"
}

register_builtin_option «instance».normalForm.wrapFields.instances : Bool := {
  defValue := true
  descr := "wrap instance fields in implicit_reducible auxiliary definitions to fix their types"
}

register_builtin_option «instance».normalForm.wrapFields.data : Bool := {
  defValue := true
  descr := "wrap data fields in auxiliary definitions to fix their types"
}

register_builtin_option «instance».normalForm.wrapFields.proofs : Bool := {
  defValue := true
  descr := "wrap proof fields in auxiliary theorems to fix their types"
}

builtin_initialize registerTraceClass `Meta.instanceNormalForm

/--
Normalize an instance value to "instance normal form":
- If the instance can be replaced by a synthesized instance, do so.
- Otherwise, reduce to a constructor application and recursively normalize
  instance-implicit fields.
- Proof fields are abstracted into auxiliary theorems.
- Data fields have their lambda binder types fixed.

This ensures that sub-instance projections (e.g., `instRing.toSemiring`) immediately
reduce to the canonical sub-instance, rather than requiring unfolding through helper functions.
-/
partial def normalizeInstance (inst expectedType : Expr) : MetaM Expr := withTransparency .instances do
  withTraceNode `Meta.instanceNormalForm
      (fun _ => return m!"type: {expectedType}") do
  let some className ← isClass? expectedType
    | return inst
  trace[Meta.instanceNormalForm] "class is {className}"
  if ← isProp expectedType then
    return inst

  let instType ← inferType inst
  if ← isDefEq instType expectedType then
    trace[Meta.instanceNormalForm] "already compatible, returning as is: {inst}"
    return inst

  -- Try to reduce it to a constructor.
  let inst ← whnf inst
  inst.withApp fun f args => do
    let some (.ctorInfo ci) ← f.constName?.mapM getConstInfo
      | do
        trace[Meta.instanceNormalForm] "did not reduce to constructor application, returning/wrapping as is: {inst}"
        if «instance».normalForm.wrapFields.instances.get (← getOptions) then
          let instType ← inferType inst
          if ← isDefEq expectedType instType then
            return inst
          else
            let name ← mkAuxDeclName
            let wrapped ← mkAuxDefinition name expectedType inst
            setReducibilityStatus name .implicitReducible
            enableRealizationsForConst name
            return wrapped
        else
          return inst
    let (mvars, _, cls) ← forallMetaTelescope (← inferType f)
    if h₁ : args.size ≠ mvars.size then
      throwError "instance normal form: incorrect number of arguments for \
        constructor application `{f}`: {args}"
    else
      unless ← isDefEq expectedType cls do
        throwError "instance normal form: `{expectedType}` does not unify with the conclusion of \
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
          -- Question: is this just redundant with `abstractNestedProofs`?
          -- Or does `mkAuxTheorem` help prevent leakage?
          if «instance».normalForm.wrapFields.proofs.get (← getOptions) then
            let argType ← inferType arg
            if ← isDefEq argExpectedType argType then
              mvarId.assign arg
            else
              mvarId.assign (← mkAuxTheorem argExpectedType arg (zetaDelta := true))
          else
            mvarId.assign arg
        -- Recurse into instance arguments of the constructor
        else if (← isClass? argExpectedType).isSome then
          mvarId.assign (← normalizeInstance arg argExpectedType)
        else
          -- For data fields, assign directly or wrap in aux def to fix types.
          if «instance».normalForm.wrapFields.data.get (← getOptions) then
            let argType ← inferType arg
            if ← isDefEq argExpectedType argType then
              mvarId.assign arg
            else
              let name ← mkAuxDeclName
              mvarId.assign (← mkAuxDefinition name argExpectedType arg)
              enableRealizationsForConst name
          else
            mvarId.assign arg
      return mkAppN f (← mvars.mapM instantiateMVars)

end Lean.Meta
