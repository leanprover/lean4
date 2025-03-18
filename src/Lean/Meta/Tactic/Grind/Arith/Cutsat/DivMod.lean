/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Grind.PropagatorAttr
import Lean.Meta.Tactic.Grind.Arith.Cutsat.Util
import Lean.Meta.Tactic.Grind.Canon
import Lean.Meta.Tactic.Grind.Core

namespace Lean.Meta.Grind.Arith.Cutsat

private def assertFact (h : Expr) : GoalM Unit := do
  let prop ← shareCommon (← canon (← inferType h))
  trace[Meta.debug] "{prop}"
  add prop h 0

private def expandDivMod (a : Expr) (b : Int) : GoalM Unit := do
  if b == 0 then return ()
  if (← get').divMod.contains (a, b) then return ()
  modify' fun s => { s with divMod := s.divMod.insert (a, b) }
  let n : Int := 1 - b.natAbs
  let b := mkIntLit b
  assertFact <| mkApp2 (mkConst ``Int.Linear.ediv_emod) a b
  assertFact <| mkApp3 (mkConst ``Int.Linear.emod_nonneg) a b reflBoolTrue
  assertFact <| mkApp4 (mkConst ``Int.Linear.emod_le) a b (toExpr n) reflBoolTrue

builtin_grind_propagator propagateDiv ↑HDiv.hDiv := fun e => do
  let_expr HDiv.hDiv _ _ _ inst a b ← e | return ()
  unless (← isInstHDivInt inst) do return ()
  let some b ← getIntValue? b | return ()
  -- Remark: we currently do not consider the case where `b` is in the equivalence class of a numeral.
  expandDivMod a b

builtin_grind_propagator propagateMod ↑HMod.hMod := fun e => do
  let_expr HMod.hMod _ _ _ inst a b ← e | return ()
  unless (← isInstHModInt inst) do return ()
  let some b ← getIntValue? b | return ()
  expandDivMod a b

end Lean.Meta.Grind.Arith.Cutsat
