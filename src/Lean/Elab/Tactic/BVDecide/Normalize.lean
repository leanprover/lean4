/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module
prelude
public import Lean.Meta.Tactic.BVDecide.Normalize

namespace Lean.Elab.Tactic.BVDecide
namespace Normalize

@[builtin_tactic Lean.Parser.Tactic.bvNormalize]
def evalBVNormalize : Tactic := fun
  | `(tactic| bv_normalize $cfg:optConfig) => do
    let cfg ← Meta.Tactic.BVDecide.elabBVDecideConfig cfg
    let g ← getMainGoal
    let (_, state) ← Meta.Tactic.BVDecide.Normalize.bvNormalize.run cfg g
    if ← state.goal.isAssigned then
      replaceMainGoal []
    else
      let hyps := state.hypotheses.map fun hyp => {
        userName := hyp.name
        type := hyp.type
        value := hyp.value
      }
      let (_, goal) ← MVarId.assertHypotheses state.goal hyps
      replaceMainGoal [goal]

  | _ => throwUnsupportedSyntax

end Normalize
end Lean.Elab.Tactic.BVDecide
