/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Grind.Arith.Cutsat.Var

namespace Lean.Meta.Grind.Arith.Cutsat

@[export lean_process_cutsat_eq]
def processNewEqImpl (a b : Expr) : GoalM Unit := do
  trace[grind.cutsat.eq] "{mkIntEq a b}"
  -- TODO
  return ()

@[export lean_process_new_cutsat_lit]
def processNewEqLitImpl (a k : Expr) : GoalM Unit := do
  trace[grind.cutsat.eq] "{mkIntEq a k}"
  -- TODO
  return ()

end Lean.Meta.Grind.Arith.Cutsat
