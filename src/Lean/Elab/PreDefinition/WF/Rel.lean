/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Elab.SyntheticMVars
import Lean.Elab.PreDefinition.Basic

namespace Lean.Elab.WF
open Meta
open Term

def elabWFRel (unaryPreDef : PreDefinition) (wfStx? : Option Syntax) : TermElabM Expr := do
  if let some wfStx := wfStx? then
    withDeclName unaryPreDef.declName do
      let α := unaryPreDef.type.bindingDomain!
      let u ← getLevel α
      let expectedType := mkApp (mkConst ``WellFoundedRelation [u]) α
      let wfRel ← instantiateMVars (← withSynthesize <| elabTermEnsuringType wfStx expectedType)
      let pendingMVarIds ← getMVars wfRel
      discard <| logUnassignedUsingErrorInfos pendingMVarIds
      return wfRel
  else
    -- TODO: try to synthesize some default relation
    throwError "'termination_by' modifier missing"

end Lean.Elab.WF
