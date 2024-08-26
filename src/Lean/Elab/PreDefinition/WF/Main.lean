/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Elab.PreDefinition.Basic
import Lean.Elab.PreDefinition.TerminationArgument
import Lean.Elab.PreDefinition.WF.PackMutual
import Lean.Elab.PreDefinition.WF.Preprocess
import Lean.Elab.PreDefinition.WF.Rel
import Lean.Elab.PreDefinition.WF.Fix
import Lean.Elab.PreDefinition.WF.Eqns
import Lean.Elab.PreDefinition.WF.Ite
import Lean.Elab.PreDefinition.WF.GuessLex

namespace Lean.Elab
open WF
open Meta

private partial def addNonRecPreDefs (fixedPrefixSize : Nat) (argsPacker : ArgsPacker) (preDefs : Array PreDefinition) (preDefNonRec : PreDefinition)  : TermElabM Unit := do
  let us := preDefNonRec.levelParams.map mkLevelParam
  let all := preDefs.toList.map (·.declName)
  for fidx in [:preDefs.size] do
    let preDef := preDefs[fidx]!
    let value ← forallBoundedTelescope preDef.type (some fixedPrefixSize) fun xs _ => do
      let value := mkAppN (mkConst preDefNonRec.declName us) xs
      let value ← argsPacker.curryProj value fidx
      mkLambdaFVars xs value
    trace[Elab.definition.wf] "{preDef.declName} := {value}"
    addNonRec { preDef with value } (applyAttrAfterCompilation := false) (all := all)

partial def withCommonTelescope (preDefs : Array PreDefinition) (k : Array Expr → Array Expr → TermElabM α) : TermElabM α :=
  go #[] (preDefs.map (·.value))
where
  go (fvars : Array Expr) (vals : Array Expr) : TermElabM α := do
    if !(vals.all fun val => val.isLambda) then
      k fvars vals
    else if !(← vals.allM fun val => isDefEq val.bindingDomain! vals[0]!.bindingDomain!) then
      k fvars vals
    else
      withLocalDecl vals[0]!.bindingName! vals[0]!.binderInfo vals[0]!.bindingDomain! fun x =>
        go (fvars.push x) (vals.map fun val => val.bindingBody!.instantiate1 x)

def getFixedPrefix (preDefs : Array PreDefinition) : TermElabM Nat :=
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

private def isOnlyOneUnaryDef (preDefs : Array PreDefinition) (fixedPrefixSize : Nat) : MetaM Bool := do
  if preDefs.size == 1 then
    lambdaTelescope preDefs[0]!.value fun xs _ => return xs.size == fixedPrefixSize + 1
  else
    return false

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

def wfRecursion (preDefs : Array PreDefinition) (termArg?s : Array (Option TerminationArgument)) : TermElabM Unit := do
  let termArgs? := termArg?s.sequenceMap id -- Either all or none, checked by `elabTerminationByHints`
  let preDefs ← preDefs.mapM fun preDef =>
    return { preDef with value := (← preprocess preDef.value) }
  let (fixedPrefixSize, argsPacker, unaryPreDef) ← withoutModifyingEnv do
    for preDef in preDefs do
      addAsAxiom preDef
    let fixedPrefixSize ← getFixedPrefix preDefs
    trace[Elab.definition.wf] "fixed prefix: {fixedPrefixSize}"
    let varNamess ← preDefs.mapM (varyingVarNames fixedPrefixSize ·)
    let argsPacker := { varNamess }
    let preDefsDIte ← preDefs.mapM fun preDef => return { preDef with value := (← iteToDIte preDef.value) }
    return (fixedPrefixSize, argsPacker, ← packMutual fixedPrefixSize argsPacker preDefsDIte)

  let wf : TerminationArguments ← do
    if let some tas := termArgs? then pure tas else
    -- No termination_by here, so use GuessLex to infer one
    guessLex preDefs unaryPreDef fixedPrefixSize argsPacker

  let preDefNonRec ← forallBoundedTelescope unaryPreDef.type fixedPrefixSize fun prefixArgs type => do
    let type ← whnfForall type
    unless type.isForall do
      throwError "wfRecursion: expected unary function type: {type}"
    let packedArgType := type.bindingDomain!
    elabWFRel preDefs unaryPreDef.declName prefixArgs argsPacker packedArgType wf fun wfRel => do
      trace[Elab.definition.wf] "wfRel: {wfRel}"
      let (value, envNew) ← withoutModifyingEnv' do
        addAsAxiom unaryPreDef
        let value ← mkFix unaryPreDef prefixArgs argsPacker wfRel (preDefs.map (·.termination.decreasingBy?))
        eraseRecAppSyntaxExpr value
      /- `mkFix` invokes `decreasing_tactic` which may add auxiliary theorems to the environment. -/
      let value ← unfoldDeclsFrom envNew value
      let unaryPreDef := { unaryPreDef with value }
      /-
      We must remove `implemented_by` attributes from the auxiliary application because
      this attribute is only relevant for code that is compiled. Moreover, the `[implemented_by <decl>]`
      attribute would check whether the `unaryPreDef` type matches with `<decl>`'s type, and produce
      and error. See issue #2899
      -/
      let unaryPreDef := unaryPreDef.filterAttrs fun attr => attr.name != `implemented_by
      return unaryPreDef
  trace[Elab.definition.wf] ">> {preDefNonRec.declName} :=\n{preDefNonRec.value}"
  let preDefs ← preDefs.mapM fun d => eraseRecAppSyntax d
  -- Do not complain if the user sets @[semireducible], which usually is a noop,
  -- we recognize that below and then do not set @[irreducible]
  withOptions (allowUnsafeReducibility.set · true) do
    if (← isOnlyOneUnaryDef preDefs fixedPrefixSize) then
      addNonRec preDefNonRec (applyAttrAfterCompilation := false)
    else
      withEnableInfoTree false do
        addNonRec preDefNonRec (applyAttrAfterCompilation := false)
      addNonRecPreDefs fixedPrefixSize argsPacker preDefs preDefNonRec
  -- We create the `_unsafe_rec` before we abstract nested proofs.
  -- Reason: the nested proofs may be referring to the _unsafe_rec.
  addAndCompilePartialRec preDefs
  let preDefs ← preDefs.mapM (abstractNestedProofs ·)
  registerEqnsInfo preDefs preDefNonRec.declName fixedPrefixSize argsPacker
  for preDef in preDefs do
    markAsRecursive preDef.declName
    generateEagerEqns preDef.declName
    applyAttributesOf #[preDef] AttributeApplicationTime.afterCompilation
    -- Unless the user asks for something else, mark the definition as irreducible
    unless preDef.modifiers.attrs.any fun a =>
      a.name = `reducible || a.name = `semireducible do
      setIrreducibleAttribute preDef.declName

builtin_initialize registerTraceClass `Elab.definition.wf

end Lean.Elab
