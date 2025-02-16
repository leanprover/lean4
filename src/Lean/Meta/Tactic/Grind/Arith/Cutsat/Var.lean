/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Grind.Arith.Cutsat.Util

namespace Lean.Meta.Grind.Arith.Cutsat

/-- Creates a new variable in the cutsat module. -/
def mkVar (expr : Expr) : GoalM Var := do
  if let some var := (← get').varMap.find? { expr } then
    return var
  let var : Var := (← get').vars.size
  trace[grind.cutsat.internalize.term] "{expr} ↦ #{var}"
  modify' fun s => { s with
    vars      := s.vars.push expr
    varMap    := s.varMap.insert { expr } var
    dvdCnstrs := s.dvdCnstrs.push none
  }
  return var

end Lean.Meta.Grind.Arith.Cutsat
