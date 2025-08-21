/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/

module

prelude
public import Lean.Elab.Tactic.Basic

public section

namespace Lean.Elab.WF

builtin_initialize
  registerDebugClass `rawDecreasingByGoal
    "Shows the raw `decreasing_by` goal including internal implementation detail \
     instead of cleaning it up with the `clean_wf` tactic. Can be enabled for debugging \
     purposes. Please report an issue if you have to use this option for other reasons."

open Lean Elab Tactic

def applyCleanWfTactic : TacticM Unit := do
  debug[rawDecreasingByGoal]
    -- Skip applying `clean_wf`
    return
  Tactic.evalTactic (← `(tactic| all_goals clean_wf))

end Lean.Elab.WF
