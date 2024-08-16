/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/

prelude
import Lean.Elab.Tactic.Basic

namespace Lean.Elab.WF

register_builtin_option debug.cleanDecreasingByGoal : Bool := {
  defValue := true
  descr    := "Cleans up internal implementation details in the proof goals presented by \
              `decreasing_by`, using the `clean_wf` tactic. Can be disabled for debugging \
              purposes. Please report an issue if you have to disable this option."
}

open Lean Elab Tactic

def applyCleanWfTactic : TacticM Unit := do
  if debug.cleanDecreasingByGoal.get (← getOptions) then
    Tactic.evalTactic (← `(tactic| all_goals clean_wf))

end Lean.Elab.WF
