/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Różowski
-/
module

prelude
public import Lean.Meta.Tactic.Cbv
public import Lean.Meta.Tactic

public section

namespace Lean.Elab.Tactic.Cbv

@[builtin_tactic Lean.Parser.Tactic.cbv] def evalCbv : Tactic := fun stx =>
  match stx with
  | `(tactic| cbv) => withMainContext do
    liftMetaTactic fun mvar => do
      match (← Lean.Meta.Tactic.Cbv.cbvGoal mvar) with
      | .none => return []
      | .some newGoal => return [newGoal]
  | _ => throwUnsupportedSyntax

end Lean.Elab.Tactic.Cbv
