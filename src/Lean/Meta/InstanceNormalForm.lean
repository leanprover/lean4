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
      (fun e => return m!"{exceptEmoji e} type: {expectedType}") do
  let some className ← isClass? expectedType
    | return inst
  trace[Meta.instanceNormalForm] "class is {className}"
  if ← isProp expectedType then
    return inst

  -- Try to synthesize a total replacement for this term.
  try
    match ← trySynthInstance expectedType with
    | .some new =>
      if ← withDefault <| isDefEq inst new then
        trace[Meta.instanceNormalForm] "replaced with synthesized instance"
        return new
      else
        trace[Meta.instanceNormalForm] "synthesized instance is not defeq, proceeding to constructor normalization"
    | _ => pure ()
  catch _ => pure ()
  -- Try to reduce it to a constructor.
  (← whnfI inst).withApp fun f args => do
    let .const c _ := f
      | trace[Meta.instanceNormalForm] "does not reduce to a constructor application, skipping"
        return inst
    let .ctorInfo ci ← getConstInfo c
      | trace[Meta.instanceNormalForm] "reduces to {c}, not a constructor, skipping"
        return inst
    let (mvars, bis, cls) ← forallMetaTelescope (← inferType f)
    unless args.size == mvars.size do
      throwError "instance normal form: incorrect number of arguments for \
        constructor application `{f}`: {args}"
    unless ← isDefEq expectedType cls do
      throwError "instance normal form: `{expectedType}` does not unify with the conclusion of \
        `{.ofConstName c}`"
    for i in ci.numParams...args.size do
      let bi := bis[i]!
      let mvarId := mvars[i]!.mvarId!
      let mvarDecl ← mvarId.getDecl
      let argExpectedType ← instantiateMVars mvarDecl.type
      let arg := args[i]!
      if ← isProp argExpectedType then
        -- For proofs, assign directly. Proof abstraction is handled by `abstractNestedProofs`.
        mvarId.assign arg
      -- Recurse into instance arguments of the constructor
      else if bi.isInstImplicit then
        mvarId.assign (← normalizeInstance arg argExpectedType)
      else
        -- For data fields, assign directly.
        mvarId.assign arg
    return mkAppN f (← mvars.mapM instantiateMVars)

end Lean.Meta
