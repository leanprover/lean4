/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Grind.Arith.Cutsat.Util

namespace Lean.Meta.Grind.Arith.Cutsat

private def DvdCnstrWithProof.get_d_a (cₚ : DvdCnstrWithProof) : GoalM (Int × Int) := do
  let d := cₚ.c.k
  let .add a _ _ := cₚ.c.p
    | throwError "internal `grind` error, unexpected divisibility constraint {indentExpr (← cₚ.denoteExpr)}"
  return (d, a)

partial def DvdCnstrWithProof.toExprProof' (cₚ : DvdCnstrWithProof) : ProofM Expr := cₚ.caching do
  match cₚ.h with
  | .expr h =>
    return h
  | .norm cₚ' =>
    return mkApp5 (mkConst ``Int.Linear.DvdCnstr.of_isNorm) (← getContext) (toExpr cₚ'.c) (toExpr cₚ.c) reflBoolTrue (← toExprProof' cₚ')
  | .divCoeffs cₚ' =>
    let k := cₚ'.c.p.gcdCoeffs cₚ'.c.k
    return mkApp6 (mkConst ``Int.Linear.DvdCnstr.of_isEqv) (← getContext) (toExpr cₚ'.c) (toExpr cₚ.c) (toExpr k) reflBoolTrue (← toExprProof' cₚ')
  | .solveCombine cₚ₁ cₚ₂ =>
    let (d₁, a₁) ← cₚ₁.get_d_a
    let (d₂, a₂) ← cₚ₂.get_d_a
    let (d, α, β) := gcdExt (a₁*d₂) (a₂*d₁)
    return mkApp10 (mkConst ``Int.Linear.DvdCnstr.solve_combine)
      (← getContext) (toExpr cₚ₁.c) (toExpr cₚ₂.c) (toExpr cₚ.c)
      (toExpr d) (toExpr α) (toExpr β) reflBoolTrue
      (← toExprProof' cₚ₁) (← toExprProof' cₚ₂)
  | .solveElim cₚ₁ cₚ₂ =>
    let (d₁, a₁) ← cₚ₁.get_d_a
    let (d₂, a₂) ← cₚ₂.get_d_a
    let (d, _, _) := gcdExt (a₁*d₂) (a₂*d₁)
    return mkApp8 (mkConst ``Int.Linear.DvdCnstr.solve_elim)
      (← getContext) (toExpr cₚ₁.c) (toExpr cₚ₂.c) (toExpr cₚ.c)
      (toExpr d) reflBoolTrue
      (← toExprProof' cₚ₁) (← toExprProof' cₚ₂)

partial def DvdCnstrWithProof.toExprProof (cₚ : DvdCnstrWithProof) : ProofM Expr := do
  mkExpectedTypeHint (← toExprProof' cₚ) (← cₚ.denoteExpr)

partial def RelCnstrWithProof.toExprProof (cₚ : RelCnstrWithProof) : ProofM Expr := do
  -- TODO
  mkSorry (← cₚ.denoteExpr) false

end Lean.Meta.Grind.Arith.Cutsat
