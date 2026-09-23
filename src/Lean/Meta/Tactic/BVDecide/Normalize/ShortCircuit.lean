/-
Copyright (c) 2025 Tobias Grosser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Grosser
-/
module

prelude
public import Lean.Meta.Tactic.BVDecide.Normalize.Basic
public import Std.Tactic.BVDecide.Normalize.BitVec
import Lean.Meta.Sym.Simp.Theorems
import Lean.Meta.Sym.Simp.Rewrite

/-!
This module contains the implementation of the short-circuiting pass, which is responsible for
applying short-circuit optimizations for `*`, e.g., translating `x1 * y == x2 * y` to
`!(!x1 == x2 && !x1 * y == x2 * y)`.
-/

namespace Lean.Meta.Tactic.BVDecide
namespace Normalize

open Std.Tactic.BVDecide.Normalize.BitVec

def shortCircuitProc : Sym.Simp.Simproc := fun e => withDoneResult do
  let_expr BEq.beq α inst lhs rhs  := e | return .rfl
  let_expr BitVec w := α | return .rfl
  let_expr HMul.hMul _ _ _ _ llhs lrhs := lhs | return .rfl
  let_expr HMul.hMul _ _ _ _ rlhs rrhs := rhs | return .rfl
  if Sym.isSameExpr llhs rlhs then
    let condition1 := mkApp (mkConst ``Bool.not) (mkApp4 (mkConst ``BEq.beq [0]) α inst lrhs rrhs)
    let condition2 := mkApp (mkConst ``Bool.not) e
    let condition ← Sym.share <|
      mkApp (mkConst ``Bool.not) (mkApp2 (mkConst ``Bool.and) condition1 condition2)
    let proof := mkApp4 (mkConst ``mul_beq_mul_short_circuit_right) w llhs lrhs rrhs
    return .step condition proof
  else if Sym.isSameExpr lrhs rrhs then
    let condition1 := mkApp (mkConst ``Bool.not) (mkApp4 (mkConst ``BEq.beq [0]) α inst llhs rlhs)
    let condition2 := mkApp (mkConst ``Bool.not) e
    let condition ← Sym.share <|
      mkApp (mkConst ``Bool.not) (mkApp2 (mkConst ``Bool.and) condition1 condition2)
    let proof := mkApp4 (mkConst ``mul_beq_mul_short_circuit_left) w llhs rlhs lrhs
    return .step condition proof
  else
    return .rfl

/--
Responsible for applying short-circuit optimizations for `*`, e.g.,
translating `x1 * y == x2 * y` to `!(!x1 == x2 && !x1 * y == x2 * y)`.
-/
public def shortCircuitPass : Pass where
  name := `shortCircuitPass
  run' := do
    let cfg ← PreProcessM.getConfig
    let config := {
      maxSteps := cfg.maxSteps
    }
    let methods := {
      post := shortCircuitProc
    }

    let goal ← PreProcessM.getTargetMVarId
    goal.withContext do
      PreProcessM.mapSimpHyps methods config

end Normalize
end Lean.Meta.Tactic.BVDecide
