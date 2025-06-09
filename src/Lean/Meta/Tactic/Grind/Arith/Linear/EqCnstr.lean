/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Grind.CommRing.Poly
import Lean.Meta.Tactic.Grind.Arith.CommRing.Reify
import Lean.Meta.Tactic.Grind.Arith.CommRing.DenoteExpr
import Lean.Meta.Tactic.Grind.Arith.Linear.Var
import Lean.Meta.Tactic.Grind.Arith.Linear.StructId
import Lean.Meta.Tactic.Grind.Arith.Linear.Reify
import Lean.Meta.Tactic.Grind.Arith.Linear.DenoteExpr
import Lean.Meta.Tactic.Grind.Arith.Linear.Proof

namespace Lean.Meta.Grind.Arith.Linear

@[export lean_process_linarith_eq]
def processNewEqImpl (a b : Expr) : GoalM Unit := do
  trace[grind.linarith.assert] "{a} = {b}"
  -- TODO

@[export lean_process_linarith_diseq]
def processNewDiseqImpl (a b : Expr) : GoalM Unit := do
  trace[grind.linarith.assert] "{a} ≠ {b}"
  -- TODO

end Lean.Meta.Grind.Arith.Linear
