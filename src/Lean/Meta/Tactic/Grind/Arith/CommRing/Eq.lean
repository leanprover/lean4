/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Grind.Simp
import Lean.Meta.Tactic.Grind.Arith.CommRing.RingId

namespace Lean.Meta.Grind.Arith.CommRing

@[export lean_process_ring_eq]
def processNewEqImpl (a b : Expr) : GoalM Unit := do
  if isSameExpr a b then return ()
  trace[grind.ring] "{← mkEq a b}"
  -- TODO

@[export lean_process_ring_diseq]
def processNewDiseqImpl (a b : Expr) : GoalM Unit := do
  trace[grind.ring] "{mkNot (← mkEq a b)}"
  -- TODO

end Lean.Meta.Grind.Arith.CommRing
