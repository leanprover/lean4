/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Elab.SyntheticMVars
import Lean.Elab.PreDefinition.Basic
import Lean.Elab.PreDefinition.WF.TerminationHint

namespace Lean.Elab.WF
open Meta
open Term

def elabWFRel (unaryPreDef : PreDefinition) (wf? : Option TerminationWF) : TermElabM Expr := do
  match wf? with
  | some (TerminationWF.core wfStx) => withDeclName unaryPreDef.declName do
      let α := unaryPreDef.type.bindingDomain!
      let u ← getLevel α
      let expectedType := mkApp (mkConst ``WellFoundedRelation [u]) α
      let wfRel ← instantiateMVars (← withSynthesize <| elabTermEnsuringType wfStx expectedType)
      let pendingMVarIds ← getMVars wfRel
      discard <| logUnassignedUsingErrorInfos pendingMVarIds
      return wfRel
  | none =>
    -- TODO: try to synthesize some default relation
    throwError "'termination_by' modifier missing"

end Lean.Elab.WF
