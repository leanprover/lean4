/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Grind.MBTC
import Lean.Meta.Tactic.Grind.Arith.Cutsat.Model

namespace Lean.Meta.Grind.Arith.Cutsat

private def hasTheoryVar (e : Expr) : GoalM Bool := do
  return (← getAssignment? (← get) (← getENode e)).isSome

private def isInterpreted (e : Expr) : GoalM Bool := do
  return isInterpretedTerm e

private def eqAssignment (a b : Expr) : GoalM Bool := do
  let some v₁ ← getAssignment? (← get) (← getENode a) | return false
  let some v₂ ← getAssignment? (← get) (← getENode b) | return false
  return v₁ == v₂

def mbtc : GoalM (Array (Expr × Expr)) := do
  Grind.mbtc {
    hasTheoryVar := hasTheoryVar
    isInterpreted := isInterpreted
    eqAssignment := eqAssignment
  }

end Lean.Meta.Grind.Arith.Cutsat
