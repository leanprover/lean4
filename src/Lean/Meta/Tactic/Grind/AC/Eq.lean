/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Types
public section
namespace Lean.Meta.Grind.AC

@[export lean_process_ac_eq]
def processNewEqImpl (a b : Expr) : GoalM Unit := do
  trace[grind.ac.assert] "{a} = {b}"
  -- TODO

@[export lean_process_ac_diseq]
def processNewDiseqImpl (a b : Expr) : GoalM Unit := do
  trace[grind.ac.assert] "{a} ≠ {b}"
  -- TODO

end Lean.Meta.Grind.AC
