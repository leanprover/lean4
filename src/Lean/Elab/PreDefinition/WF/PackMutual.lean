/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.ArgsPacker
import Lean.Elab.PreDefinition.Basic

namespace Lean.Elab.WF
open Meta

/--
  Pass the first `n` arguments of `e` to the continuation, and apply the result to the
  remaining arguments. If `e` does not have enough arguments, it is eta-expanded as needed.

  Unlike `Meta.etaExpand` does not use `withDefault`.
-/
def withAppN (n : Nat) (e : Expr) (k : Array Expr → MetaM Expr) : MetaM Expr := do
  let args := e.getAppArgs
  if n ≤ args.size then
    let e' ← k args[:n]
    return mkAppN e' args[n:]
  else
    let missing := n - args.size
    forallBoundedTelescope (← inferType e) missing fun xs _ => do
      if xs.size < missing then
        throwError "Failed to eta-expand partial application"
      let e' ← k (args ++ xs)
      mkLambdaFVars xs e'

/--
A `post` for `Meta.transform` to replace recursive calls to the original `preDefs` with calls
to the new unary function `newfn`.
-/
private partial def post (fixedPrefix : Nat) (argsPacker : ArgsPacker) (funNames : Array Name)
    (domain : Expr) (newFn : Name) (e : Expr) : MetaM TransformStep := do
  let f := e.getAppFn
  if !f.isConst then
    return TransformStep.done e
  let declName := f.constName!
  let us       := f.constLevels!
  if let some fidx := funNames.indexOf? declName then
    let arity := fixedPrefix + argsPacker.varNamess[fidx]!.size
    let e' ← withAppN arity e fun args => do
      let fixedArgs := args[:fixedPrefix]
      let packedArg ← argsPacker.pack domain fidx args[fixedPrefix:]
      return mkApp (mkAppN (mkConst newFn us) fixedArgs) packedArg
    return TransformStep.done e'
  return TransformStep.done e

/--
Creates a single unary function from the given `preDefs`, using the machinery in the `ArgPacker`
module.
-/
def packMutual (fixedPrefix : Nat) (argsPacker : ArgsPacker) (preDefs : Array PreDefinition) : MetaM PreDefinition := do
  let arities := argsPacker.arities
  if let #[1] := arities then return preDefs[0]!
  let newFn := if argsPacker.numFuncs > 1 then preDefs[0]!.declName ++ `_mutual
                                          else preDefs[0]!.declName ++ `_unary
  -- Bring the fixed Prefix into scope
  forallBoundedTelescope preDefs[0]!.type (some fixedPrefix) fun ys _ => do
    let types ← preDefs.mapM (instantiateForall ·.type ys)
    let vals ← preDefs.mapM (instantiateLambda ·.value ys)

    let type ← argsPacker.uncurryType types
    let packedDomain := type.bindingDomain!

    -- Temporarily add the unary function as an axiom, so that all expressions
    -- are still type correct
    let type ← mkForallFVars ys type
    let preDefNew := { preDefs[0]! with declName := newFn, type }
    addAsAxiom preDefNew

    let value ← argsPacker.uncurry vals
    let value ← transform value (skipConstInApp := true)
      (post := post fixedPrefix argsPacker (preDefs.map (·.declName)) packedDomain newFn)
    let value ← mkLambdaFVars ys value
    return { preDefNew with value }

end Lean.Elab.WF
