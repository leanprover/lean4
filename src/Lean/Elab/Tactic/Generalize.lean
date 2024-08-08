/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
prelude
import Lean.Meta.Tactic.Generalize
import Lean.Meta.Check
import Lean.Meta.Tactic.Intro
import Lean.Elab.Binders
import Lean.Elab.Tactic.ElabTerm
import Lean.Elab.Tactic.Location

namespace Lean.Elab.Tactic
open Meta

@[builtin_tactic Lean.Parser.Tactic.generalize] def evalGeneralize : Tactic := fun stx =>
  withMainContext do
    let mut xIdents := #[]
    let mut hIdents := #[]
    let mut args := #[]
    for arg in stx[1].getSepArgs do
      let hName? ← if arg[0].isNone then
        pure none
      else
        hIdents := hIdents.push arg[0][0]
        pure (some arg[0][0].getId)
      let expr ← elabTerm arg[1] none
      xIdents := xIdents.push arg[3]
      args := args.push { hName?, expr, xName? := arg[3].getId : GeneralizeArg }
    let hyps ← match expandOptLocation stx[2] with
    | .targets hyps _ => getFVarIds hyps
    | .wildcard => pure ((← getLocalHyps).map (·.fvarId!))
    let mvarId ← getMainGoal
    mvarId.withContext do
      let (_, newVars, mvarId) ← mvarId.generalizeHyp args hyps
      mvarId.withContext do
        for v in newVars, id in xIdents ++ hIdents do
          Term.addLocalVarInfo id (.fvar v)
        replaceMainGoal [mvarId]

end Lean.Elab.Tactic
