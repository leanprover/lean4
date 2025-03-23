/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Grind.Combinators
import Lean.Meta.Tactic.Grind.Canon
import Lean.Meta.Tactic.Grind.MBTC
import Lean.Meta.Tactic.Grind.Arith.Cutsat.Model

namespace Lean.Meta.Grind.Arith.Cutsat

private def hasTheoryVar (e : Expr) : GoalM Bool := do
  return (← getAssignment? (← get) (← getENode e)).isSome

private def isInterpreted (e : Expr) : GoalM Bool := do
  if isInterpretedTerm e then return true
  let f := e.getAppFn
  return f.isConstOf ``LE.le || f.isConstOf ``Dvd.dvd

private def eqAssignment (a b : Expr) : GoalM Bool := do
  let some v₁ ← getAssignment? (← get) (← getENode a) | return false
  let some v₂ ← getAssignment? (← get) (← getENode b) | return false
  return v₁ == v₂

def mbtcTac : GrindTactic :=
  Grind.mbtcTac {
    hasTheoryVar := hasTheoryVar
    isInterpreted := isInterpreted
    eqAssignment := eqAssignment
  }

end Lean.Meta.Grind.Arith.Cutsat
