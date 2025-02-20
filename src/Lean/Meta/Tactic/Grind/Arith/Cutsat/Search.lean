/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Grind.Arith.Cutsat.Var
import Lean.Meta.Tactic.Grind.Arith.Cutsat.Util
import Lean.Meta.Tactic.Grind.Arith.Cutsat.RelCnstr

namespace Lean.Meta.Grind.Arith.Cutsat

private def throwUnexpectedCnstr (cₚ : RelCnstrWithProof) : GoalM α := do
  throwError "`grind` internal error, unexpected{indentExpr (← cₚ.denoteExpr)} "

def getBestLower? (x : Var) : GoalM (Option (Int × RelCnstrWithProof)) := do
  let s ← get'
  let mut best? := none
  for cₚ in s.lowers[x]! do
    let .add k _ p := cₚ.c.p
      | throwUnexpectedCnstr cₚ
    let some v ← p.eval?
      | pure ()
    let lower' := Int.Linear.cdiv v (-k)
    if let some (lower, _) := best? then
      if lower' > lower then
        best? := some (lower', cₚ)
    else
      best? := some (lower', cₚ)
  return best?

def getBestUpper? (x : Var) : GoalM (Option (Int × RelCnstrWithProof)) := do
  let s ← get'
  let mut best? := none
  for cₚ in s.uppers[x]! do
    let .add k _ p := cₚ.c.p
      | throwUnexpectedCnstr cₚ
    let some v ← p.eval?
      | pure ()
    let upper' := (-v) / k
    if let some (upper, _) := best? then
      if upper' < upper then
        best? := some (upper', cₚ)
    else
      best? := some (upper', cₚ)
  return best?

end Lean.Meta.Grind.Arith.Cutsat
