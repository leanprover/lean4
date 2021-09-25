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

def elabWF (unaryPreDef : PreDefinition) (wfStx? : Option Syntax) : TermElabM (Expr × Expr) := do
  if let some wfStx := wfStx? then
    withDeclName unaryPreDef.declName do
      let α := unaryPreDef.type.bindingDomain!
      let u ← getLevel α
      let r ← mkFreshExprMVar (← mkArrow α (← mkArrow α (mkSort levelZero)))
      let expectedType := mkApp2 (mkConst ``WellFounded [u]) α r
      let w ← instantiateMVars (← withSynthesize <| elabTermEnsuringType wfStx expectedType)
      let r ← instantiateMVars r
      let pendingMVarIds ← getMVars w
      discard <| logUnassignedUsingErrorInfos pendingMVarIds
      return (r, w)
  else
    -- TODO: try to synthesize some default relation
    throwError "'termination_by' modifier missing"

end Lean.Elab.WF
