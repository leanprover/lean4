/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
import Lean.Meta.Tactic.Generalize
import Lean.Meta.Check
import Lean.Meta.Tactic.Intro
import Lean.Elab.Tactic.ElabTerm
import Lean.Elab.Tactic.Location

namespace Lean.Elab.Tactic
open Meta

@[builtin_tactic Lean.Parser.Tactic.generalize] def evalGeneralize : Tactic := fun stx =>
  withMainContext do
    let args ← stx[1].getSepArgs.mapM fun arg => do
      let hName? := if arg[0].isNone then none else some arg[0][0].getId
      let expr ← elabTerm arg[1] none
      return { hName?, expr, xName? := arg[3].getId : GeneralizeArg }
    let hyps ← match expandOptLocation stx[2] with
    | .targets hyps _ => getFVarIds hyps
    | .wildcard => pure (← getLCtx).getFVarIds
    liftMetaTactic fun mvarId => do
      let (_, _, mvarId) ← mvarId.generalizeHyp args hyps
      return [mvarId]

end Lean.Elab.Tactic
