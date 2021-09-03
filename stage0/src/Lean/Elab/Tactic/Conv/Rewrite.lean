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

def evalRewriteCore (mode : TransparencyMode) : Tactic := fun stx =>
  withRWRulesSeq stx[0] stx[1] fun symm term => do
    Term.withSynthesize <| withMainContext do
      let e ← elabTerm term none true
      let r ← rewrite (← getMainGoal) (← getLhs) e symm (mode := mode)
      updateLhs r.eNew r.eqProof
      replaceMainGoal ((← getMainGoal) :: r.mvarIds)

@[builtinTactic Lean.Parser.Tactic.Conv.rewrite] def evalRewrite : Tactic :=
  evalRewriteCore TransparencyMode.instances

@[builtinTactic Lean.Parser.Tactic.Conv.erewrite] def evalERewrite : Tactic :=
  evalRewriteCore TransparencyMode.default

end Lean.Elab.Tactic.Conv
