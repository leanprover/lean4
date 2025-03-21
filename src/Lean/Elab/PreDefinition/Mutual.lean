/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Joachim Breitner
-/
prelude
import Lean.Elab.PreDefinition.Basic

/-!
This module contains code common to mutual-via-fixedpoint constructions, i.e.
well-founded recursion and partial fixed-points, but independent of the details of the mutual packing.
-/

namespace Lean.Elab.Mutual
open Meta

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

def addPreDefsFromUnary (preDefs : Array PreDefinition) (preDefsNonrec : Array PreDefinition)
    (unaryPreDefNonRec : PreDefinition) : TermElabM Unit := do
  /-
  We must remove `implemented_by` attributes from the auxiliary application because
  this attribute is only relevant for code that is compiled. Moreover, the `[implemented_by <decl>]`
  attribute would check whether the `unaryPreDef` type matches with `<decl>`'s type, and produce
  and error. See issue #2899
  -/
  let preDefNonRec := unaryPreDefNonRec.filterAttrs fun attr => attr.name != `implemented_by
  let declNames := preDefs.toList.map (·.declName)

  -- Do not complain if the user sets @[semireducible], which usually is a noop,
  -- we recognize that below and then do not set @[irreducible]
  withOptions (allowUnsafeReducibility.set · true) do
    if unaryPreDefNonRec.declName = preDefs[0]!.declName then
      addNonRec preDefNonRec (applyAttrAfterCompilation := false)
    else
      withEnableInfoTree false do
        addNonRec preDefNonRec (applyAttrAfterCompilation := false)
      preDefsNonrec.forM (addNonRec · (applyAttrAfterCompilation := false) (all := declNames))

/--
Cleans the right-hand-sides of the predefinitions, to prepare for inclusion in the EqnInfos:
 * Remove RecAppSyntax markers
 * Abstracts nested proofs (and for that, add the `_unsafe_rec` definitions)
-/
def cleanPreDefs (preDefs : Array PreDefinition) : TermElabM (Array PreDefinition) := do
  addAndCompilePartialRec preDefs
  let preDefs ← preDefs.mapM (eraseRecAppSyntax ·)
  let preDefs ← preDefs.mapM (abstractNestedProofs ·)
  return preDefs

/--
Assign final attributes to the definitions. Assumes the EqnInfos to be already present.
-/
def addPreDefAttributes (preDefs : Array PreDefinition) : TermElabM Unit := do
  for preDef in preDefs do
    markAsRecursive preDef.declName
    -- must happen before `generateEagerEqns`
    enableRealizationsForConst preDef.declName
    generateEagerEqns preDef.declName
    applyAttributesOf #[preDef] AttributeApplicationTime.afterCompilation
    -- Unless the user asks for something else, mark the definition as irreducible
    unless preDef.modifiers.attrs.any fun a =>
      a.name = `reducible || a.name = `semireducible do
      setIrreducibleAttribute preDef.declName

end Lean.Elab.Mutual
