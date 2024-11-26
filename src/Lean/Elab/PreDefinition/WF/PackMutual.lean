/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Joachim Breitner
-/
prelude
import Lean.Meta.ArgsPacker
import Lean.Elab.PreDefinition.Basic
import Lean.Elab.PreDefinition.WF.Eqns

/-!
This module contains roughtl everything need to turn mutual n-ary functions into a single unary
function, and is shared between well-founded recursion and tailrecursion
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

/--
Collect the names of the varying variables (after the fixed prefix); this also determines the
arity for the well-founded translations, and is turned into an `ArgsPacker`.
We use the term to determine the arity, but take the name from the type, for better names in the
```
fun : (n : Nat) → Nat | 0 => 0 | n+1 => fun n
```
idiom.
-/
def varyingVarNames (fixedPrefixSize : Nat) (preDef : PreDefinition) : MetaM (Array Name) := do
  -- We take the arity from the term, but the names from the types
  let arity ← lambdaTelescope preDef.value fun xs _ => return xs.size
  assert! fixedPrefixSize ≤ arity
  if arity = fixedPrefixSize then
    throwError "well-founded recursion cannot be used, '{preDef.declName}' does not take any (non-fixed) arguments"
  forallBoundedTelescope preDef.type arity fun xs _ => do
    assert! xs.size = arity
    let xs : Array Expr := xs[fixedPrefixSize:]
    xs.mapM (·.fvarId!.getUserName)


partial def withCommonTelescope (preDefs : Array PreDefinition) (k : Array Expr → Array Expr → MetaM α) : MetaM α :=
  go #[] (preDefs.map (·.value))
where
  go (fvars : Array Expr) (vals : Array Expr) : MetaM α := do
    if !(vals.all fun val => val.isLambda) then
      k fvars vals
    else if !(← vals.allM fun val => isDefEq val.bindingDomain! vals[0]!.bindingDomain!) then
      k fvars vals
    else
      withLocalDecl vals[0]!.bindingName! vals[0]!.binderInfo vals[0]!.bindingDomain! fun x =>
        go (fvars.push x) (vals.map fun val => val.bindingBody!.instantiate1 x)

def getFixedPrefix (preDefs : Array PreDefinition) : MetaM Nat :=
  withCommonTelescope preDefs fun xs vals => do
    let resultRef ← IO.mkRef xs.size
    for val in vals do
      if (← resultRef.get) == 0 then return 0
      forEachExpr' val fun e => do
        if preDefs.any fun preDef => e.isAppOf preDef.declName then
          let args := e.getAppArgs
          resultRef.modify (min args.size ·)
          for arg in args, x in xs do
            if !(← withoutProofIrrelevance <| withReducible <| isDefEq arg x) then
              -- We continue searching if e's arguments are not a prefix of `xs`
              return true
          return false
        else
          return true
    resultRef.get

def mkUnaryPreDef (preDefs : Array PreDefinition) : MetaM (Nat × ArgsPacker × PreDefinition) :=
  withoutModifyingEnv do
    for preDef in preDefs do
      addAsAxiom preDef
    let fixedPrefixSize ← getFixedPrefix preDefs
    trace[Elab.definition.wf] "fixed prefix: {fixedPrefixSize}"
    let varNamess ← preDefs.mapM (varyingVarNames fixedPrefixSize ·)
    let argsPacker := { varNamess }
    return (fixedPrefixSize, argsPacker, ← packMutual fixedPrefixSize argsPacker preDefs)

private partial def addNonRecPreDefs (fixedPrefixSize : Nat) (argsPacker : ArgsPacker) (preDefs : Array PreDefinition) (preDefNonRec : PreDefinition)  : TermElabM Unit := do
  let us := preDefNonRec.levelParams.map mkLevelParam
  let all := preDefs.toList.map (·.declName)
  for h : fidx in [:preDefs.size] do
    let preDef := preDefs[fidx]
    let value ← forallBoundedTelescope preDef.type (some fixedPrefixSize) fun xs _ => do
      let value := mkAppN (mkConst preDefNonRec.declName us) xs
      let value ← argsPacker.curryProj value fidx
      mkLambdaFVars xs value
    trace[Elab.definition.wf] "{preDef.declName} := {value}"
    addNonRec { preDef with value } (applyAttrAfterCompilation := false) (all := all)

def addPreDefsFromUnary (preDefs : Array PreDefinition) (fixedPrefixSize : Nat)
    (argsPacker : ArgsPacker) (preDefNonRec : PreDefinition) (hasInduct : Bool) : TermElabM Unit := do
  /-
  We must remove `implemented_by` attributes from the auxiliary application because
  this attribute is only relevant for code that is compiled. Moreover, the `[implemented_by <decl>]`
  attribute would check whether the `unaryPreDef` type matches with `<decl>`'s type, and produce
  and error. See issue #2899
  -/
  let preDefNonRec := preDefNonRec.filterAttrs fun attr => attr.name != `implemented_by

  -- Do not complain if the user sets @[semireducible], which usually is a noop,
  -- we recognize that below and then do not set @[irreducible]
  withOptions (allowUnsafeReducibility.set · true) do
    if argsPacker.onlyOneUnary then
      addNonRec preDefNonRec (applyAttrAfterCompilation := false)
    else
      withEnableInfoTree false do
        addNonRec preDefNonRec (applyAttrAfterCompilation := false)
      addNonRecPreDefs fixedPrefixSize argsPacker preDefs preDefNonRec

  -- We create the `_unsafe_rec` before we abstract nested proofs.
  -- Reason: the nested proofs may be referring to the _unsafe_rec.
  addAndCompilePartialRec preDefs
  let preDefs ← preDefs.mapM (eraseRecAppSyntax ·)
  let preDefs ← preDefs.mapM (abstractNestedProofs ·)
  registerEqnsInfo preDefs preDefNonRec.declName fixedPrefixSize argsPacker hasInduct
  for preDef in preDefs do
    markAsRecursive preDef.declName
    generateEagerEqns preDef.declName
    applyAttributesOf #[preDef] AttributeApplicationTime.afterCompilation
    -- Unless the user asks for something else, mark the definition as irreducible
    unless preDef.modifiers.attrs.any fun a =>
      a.name = `reducible || a.name = `semireducible do
      setIrreducibleAttribute preDef.declName


end Lean.Elab.WF
