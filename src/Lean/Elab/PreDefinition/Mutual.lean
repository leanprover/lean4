/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Joachim Breitner
-/
module

prelude
public import Lean.Elab.PreDefinition.Basic

public section

/-!
This module contains code common to mutual-via-fixedpoint constructions, i.e.
well-founded recursion and partial fixed-points, but independent of the details of the mutual packing.
-/

namespace Lean.Elab.Mutual
open Meta

def addPreDefsFromUnary (docCtx : LocalContext × LocalInstances) (preDefs : Array PreDefinition) (preDefsNonrec : Array PreDefinition)
    (unaryPreDefNonRec : PreDefinition) (cacheProofs := true) : TermElabM Unit := do
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
      addNonRec docCtx preDefNonRec (applyAttrAfterCompilation := false) (cacheProofs := cacheProofs)
        (isRecursive := true)
    else
      withEnableInfoTree false do
        addNonRec docCtx preDefNonRec (applyAttrAfterCompilation := false) (cacheProofs := cacheProofs)
          (isRecursive := true)
      preDefsNonrec.forM fun preDefNonRec =>
        addNonRec docCtx preDefNonRec (applyAttrAfterCompilation := false) (all := declNames)
          (cacheProofs := cacheProofs) (isRecursive := true)

/--
Cleans the right-hand-sides of the predefinitions, to prepare for inclusion in the EqnInfos:
 * Remove RecAppSyntax markers
 * Abstracts nested proofs (and for that, add the `_unsafe_rec` definitions)
-/
def cleanPreDef (preDef : PreDefinition) (cacheProofs := true) : MetaM PreDefinition := do
  let preDef ← eraseRecAppSyntax preDef
  let preDef ← abstractNestedProofs (cache := cacheProofs) preDef
  return preDef

/--
Assign final attributes to the definitions. Assumes the EqnInfos to be already present.
-/
def addPreDefAttributes (preDefs : Array PreDefinition) : TermElabM Unit := do
  /-
  Set irreducibility attribute, unless the user has requested a different setting.
  Must appen before `enableRealizationsForConst`, else the equation generation sees
  a wrong setting and creates bad `defEq` equations.
  -/
  for preDef in preDefs do
    unless preDef.modifiers.attrs.any fun a => a.name = `reducible || a.name = `semireducible do
      setIrreducibleAttribute preDef.declName

  /-
  `enableRealizationsForConst` must happen before `generateEagerEqns`
  It must happen in reverse order so that constants realized as part of the first decl
  have realizations for the other ones enabled
  -/
  for preDef in preDefs.reverse do
    enableRealizationsForConst preDef.declName

  for preDef in preDefs do
    generateEagerEqns preDef.declName
    applyAttributesOf #[preDef] AttributeApplicationTime.afterCompilation

end Lean.Elab.Mutual
