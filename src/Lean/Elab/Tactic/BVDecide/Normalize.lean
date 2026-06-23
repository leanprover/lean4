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
    match ← Meta.Tactic.BVDecide.Normalize.bvNormalize g cfg with
    | some newGoal => replaceMainGoal [newGoal]
    | none => replaceMainGoal []
  | _ => throwUnsupportedSyntax

end Normalize
end Lean.Elab.Tactic.BVDecide
