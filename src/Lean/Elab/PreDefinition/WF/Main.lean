/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Elab.PreDefinition.Basic
import Lean.Elab.PreDefinition.WF.TerminationBy
import Lean.Elab.PreDefinition.WF.PackDomain
import Lean.Elab.PreDefinition.WF.PackMutual
import Lean.Elab.PreDefinition.WF.Rel
import Lean.Elab.PreDefinition.WF.Fix

namespace Lean.Elab
open WF
open Meta

def wfRecursion (preDefs : Array PreDefinition) (wfStx? : Option Syntax) : TermElabM Unit := do
  let unaryPreDef ← withoutModifyingEnv do
    for preDef in preDefs do
      addAsAxiom preDef
    let unaryPreDefs ← packDomain preDefs
    packMutual unaryPreDefs
  let wfRel ← elabWFRel unaryPreDef wfStx?
  let preDefNonRec ← withoutModifyingEnv do
    addAsAxiom unaryPreDef
    mkFix unaryPreDef wfRel
  addNonRec preDefNonRec
  -- TODO: define preDefs
  -- addAndCompilePartialRec preDefs

builtin_initialize registerTraceClass `Elab.definition.wf

end Lean.Elab
