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
partial def normalizeInstance (inst expectedType : Expr) : MetaM Expr := withReducible do
  withTraceNode `Meta.instanceNormalForm
      (fun _ => return m!"type: {expectedType}") do
  let some className ← isClass? expectedType
    | return inst
  trace[Meta.instanceNormalForm] "class is {className}"
  if ← isProp expectedType then
    return inst

  withTransparency .instances do

  -- Try to synthesize a total replacement for this term.
  try
    match ← trySynthInstance expectedType with
    | .some new =>
      if ← isDefEq inst new then
        trace[Meta.instanceNormalForm] "replaced with synthesized instance"
        return new
      else
        trace[Meta.instanceNormalForm] "synthesized instance is not defeq, proceeding to constructor normalization"
    | _ => pure ()
  catch _ => pure ()
  -- Try to reduce it to a constructor.
  (← whnf inst).withApp fun f args => do
    let .const c _ := f
      | trace[Meta.instanceNormalForm] "does not reduce to a constructor application, skipping"
        return inst
    let .ctorInfo ci ← getConstInfo c
      | trace[Meta.instanceNormalForm] "reduces to {c}, not a constructor, skipping"
        return inst
    let (mvars, _, cls) ← forallMetaTelescope (← inferType f)
    if h₁ : args.size ≠ mvars.size then
      throwError "instance normal form: incorrect number of arguments for \
        constructor application `{f}`: {args}"
    else
      unless ← isDefEq expectedType cls do
        throwError "instance normal form: `{expectedType}` does not unify with the conclusion of \
          `{.ofConstName c}`"
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
          let normalized ← normalizeInstance arg argExpectedType
          if «instance».normalForm.wrapFields.instances.get (← getOptions) then
            let normalizedType ← inferType normalized
            if ← isDefEq argExpectedType normalizedType then
              mvarId.assign normalized
            else
              let name ← mkAuxDeclName
              let wrapped ← mkAuxDefinition name argExpectedType normalized
              setReducibilityStatus name .implicitReducible
              mvarId.assign wrapped
          else
            mvarId.assign normalized
        else
          -- For data fields, assign directly or wrap in aux def to fix types.
          if «instance».normalForm.wrapFields.data.get (← getOptions) then
            let argType ← inferType arg
            if ← isDefEq argExpectedType argType then
              mvarId.assign arg
            else
              let name ← mkAuxDeclName
              mvarId.assign (← mkAuxDefinition name argExpectedType arg)
          else
            mvarId.assign arg
      return mkAppN f (← mvars.mapM instantiateMVars)

end Lean.Meta
