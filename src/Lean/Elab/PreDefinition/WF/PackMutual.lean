/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Joachim Breitner
-/
prelude
import Lean.Meta.ArgsPacker
import Lean.Elab.PreDefinition.Basic
import Lean.Elab.PreDefinition.Mutual
import Lean.Elab.PreDefinition.WF.Eqns

/-!
This module contains roughly everything neede to turn mutual n-ary functions into a single unary
function, as used by well-founded recursion.
-/

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
Processes the expression and replaces calls to  the `preDefs` with calls to `f`.
-/
def packCalls (fixedParams : Mutual.FixedParams) (argsPacker : ArgsPacker) (funNames : Array Name) (newF : Expr)
  (e : Expr) : MetaM Expr := do
  let fType ← inferType newF
  unless fType.isForall do
    throwError "Not a forall: {newF} : {fType}"
  let domain := fType.bindingDomain!
  transform e (skipConstInApp := true) (post := fun e => do
    let f := e.getAppFn
    if !f.isConst then
      return TransformStep.done e
    if let some fidx := funNames.idxOf? f.constName! then
      assert! fidx < fixedParams.mappings.size
      let mask := fixedParams.mappings[fidx]!.map Option.isSome
      let arity := mask.size
      let e' ← withAppN arity e fun args => do
        let varying := Mutual.pickVaryingArgs fixedParams fidx args
        let packedArg ← argsPacker.pack domain fidx varying
        return mkApp newF packedArg
      return TransformStep.done e'
    return TransformStep.done e
    )

def mutualName (fixedParams : Mutual.FixedParams) (argsPacker : ArgsPacker) (preDefs : Array PreDefinition) : Name :=
  if fixedParams.fixedArePrefix && argsPacker.onlyOneUnary then
    preDefs[0]!.declName
  else
    if argsPacker.numFuncs > 1 then
      preDefs[0]!.declName ++ `_mutual
    else
      preDefs[0]!.declName ++ `_unary

/--
Creates a single unary function from the given `preDefs`, using the machinery in the `ArgPacker`
module.
-/
def packMutual (fixedParams : Mutual.FixedParams) (argsPacker : ArgsPacker) (preDefs : Array PreDefinition) : MetaM PreDefinition := do
  let newFn := mutualName fixedParams argsPacker preDefs
  if newFn = preDefs[0]!.declName then
    return preDefs[0]!
  -- Bring the fixed prefix into scope
  Mutual.forallTelescopeFixedParams fixedParams 0 preDefs[0]!.type fun ys => do
    let types ← preDefs.mapIdxM fun i preDef =>
      Mutual.instantiateForallFixedParams fixedParams i preDef.type ys
    let vals ← preDefs.mapIdxM fun i preDef =>
      Mutual.instantiateLambdaFixedParams fixedParams i preDef.value ys

    let type ← argsPacker.uncurryType types

    -- Temporarily add the unary function as an axiom, so that all expressions
    -- are still type correct
    let type ← mkForallFVars ys type
    let preDefNew := { preDefs[0]! with declName := newFn, type }
    addAsAxiom preDefNew

    let us := preDefs[0]!.levelParams.map mkLevelParam
    let f := mkAppN (mkConst newFn us) ys

    let value ← argsPacker.uncurry vals
    let value ← packCalls fixedParams argsPacker (preDefs.map (·.declName)) f value
    let value ← mkLambdaFVars ys value
    return { preDefNew with value }

/--
Collect the names of the varying variables (excluding the fixed parameters); this also determines the
arity for the well-founded translations, and is turned into an `ArgsPacker`.
We use the term to determine the arity, but take the name from the type, for better names in the
```
fun : (n : Nat) → Nat | 0 => 0 | n+1 => fun n
```
idiom.
-/
def varyingVarNames (fixedParams : Mutual.FixedParams) (preDefIdx : Nat) (preDef : PreDefinition) : MetaM (Array Name) := do
  -- We take the arity from the term, but the names from the types
  let arity ← lambdaTelescope preDef.value fun xs _ => return xs.size
  forallBoundedTelescope preDef.type arity fun xs _ => do
    assert! xs.size = arity
    assert! fixedParams.mappings[preDefIdx]!.size = arity
    let mut ns := #[]
    for x in xs, paramInfo in fixedParams.mappings[preDefIdx]! do
      if paramInfo.isSome then continue -- skip fixed parameters
      ns := ns.push (← x.fvarId!.getUserName)
    return ns

def preDefsFromUnaryNonRec (fixedParams : Mutual.FixedParams) (argsPacker : ArgsPacker)
    (preDefs : Array PreDefinition) (unaryPreDefNonRec : PreDefinition) : MetaM (Array PreDefinition) := do
  withoutModifyingEnv do
    let us := unaryPreDefNonRec.levelParams.map mkLevelParam
    addAsAxiom unaryPreDefNonRec
    preDefs.mapIdxM fun fidx preDef => do
      let arity := fixedParams.mappings[fidx]!.size
      let value ← forallBoundedTelescope preDef.type (some arity) fun params _ => do
        assert! arity = params.size
        let xs := Mutual.pickFixedArgs fixedParams fidx params
        let ys := Mutual.pickVaryingArgs fixedParams fidx params
        let value := mkAppN (mkConst unaryPreDefNonRec.declName us) xs
        let value ← argsPacker.curryProj value fidx
        let value := value.beta ys
        mkLambdaFVars params value
      trace[Elab.definition.wf] "{preDef.declName} := {value}"
      pure { preDef with value }

end Lean.Elab.WF
