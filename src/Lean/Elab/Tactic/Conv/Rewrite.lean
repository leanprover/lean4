/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Tactic.Rewrite
import Lean.Elab.Tactic.Rewrite
import Lean.Elab.Tactic.Conv.Basic

namespace Lean.Elab.Tactic.Conv
open Meta

@[builtin_tactic Lean.Parser.Tactic.Conv.rewrite] def evalRewrite : Tactic := fun stx => do
  let config ← Tactic.elabRewriteConfig stx[1]
  withRWRulesSeq stx[0] stx[2] fun symm term => do
    Term.withSynthesize <| withMainContext do
      let e ← elabTerm term none true
      let r ←  (← getMainGoal).rewrite (← getLhs) e symm (config := config)
      updateLhs r.eNew r.eqProof
      replaceMainGoal ((← getMainGoal) :: r.mvarIds)

end Lean.Elab.Tactic.Conv
