/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Grind.Arith.Cutsat.Util

namespace Lean.Meta.Grind.Arith.Cutsat

private def DvdCnstr.get_d_a (c : DvdCnstr) : GoalM (Int × Int) := do
  let d := c.d
  let .add a _ _ := c.p | c.throwUnexpected
  return (d, a)

mutual
partial def DvdCnstr.toExprProof (c' : DvdCnstr) : ProofM Expr := c'.caching do
  match c'.h with
  | .expr h =>
    return h
  | .norm c =>
    return mkApp6 (mkConst ``Int.Linear.dvd_norm) (← getContext) (toExpr c.d) (toExpr c.p) (toExpr c'.p) reflBoolTrue (← c.toExprProof)
  | .elim c =>
    return mkApp7 (mkConst ``Int.Linear.dvd_elim) (← getContext) (toExpr c.d) (toExpr c.p) (toExpr c'.d) (toExpr c'.p) reflBoolTrue (← c.toExprProof)
  | .divCoeffs c =>
    let g := c.p.gcdCoeffs c.d
    return mkApp8 (mkConst ``Int.Linear.dvd_coeff) (← getContext) (toExpr c.d) (toExpr c.p) (toExpr c'.d) (toExpr c'.p) (toExpr g) reflBoolTrue (← c.toExprProof)
  | .solveCombine c₁ c₂ =>
    let (d₁, a₁) ← c₁.get_d_a
    let (d₂, a₂) ← c₂.get_d_a
    let (g, α, β) := gcdExt (a₁*d₂) (a₂*d₁)
    let r := mkApp10 (mkConst ``Int.Linear.dvd_solve_combine)
      (← getContext) (toExpr c₁.d) (toExpr c₁.p) (toExpr c₂.d) (toExpr c₂.p) (toExpr c'.d) (toExpr c'.p)
      (toExpr g) (toExpr α) (toExpr β)
    return mkApp3 r reflBoolTrue (← c₁.toExprProof) (← c₂.toExprProof)
  | .solveElim c₁ c₂ =>
    return mkApp10 (mkConst ``Int.Linear.dvd_solve_elim)
      (← getContext) (toExpr c₁.d) (toExpr c₁.p) (toExpr c₂.d) (toExpr c₂.p) (toExpr c'.d) (toExpr c'.p)
      reflBoolTrue (← c₁.toExprProof) (← c₂.toExprProof)
  | .subst _c₁ _c₂ => throwError "NIY"
  | .ofEq _c => throwError "NIY"

partial def LeCnstr.toExprProof (c' : LeCnstr) : ProofM Expr := c'.caching do
  match c'.h with
  | .expr h =>
    return h
  | .norm c =>
    return mkApp5 (mkConst ``Int.Linear.le_norm) (← getContext) (toExpr c.p) (toExpr c'.p) reflBoolTrue (← c.toExprProof)
  | .divCoeffs c =>
    let k := c.p.gcdCoeffs'
    return mkApp6 (mkConst ``Int.Linear.le_coeff) (← getContext) (toExpr c.p) (toExpr c'.p) (toExpr (Int.ofNat k)) reflBoolTrue (← c.toExprProof)
  | .notExpr p h =>
    return mkApp5 (mkConst ``Int.Linear.le_neg) (← getContext) (toExpr p) (toExpr c'.p) reflBoolTrue h
  | .combine c₁ c₂ =>
    return mkApp7 (mkConst ``Int.Linear.le_combine)
      (← getContext) (toExpr c₁.p) (toExpr c₂.p) (toExpr c'.p)
      reflBoolTrue
      (← c₁.toExprProof) (← c₂.toExprProof)
  | .subst _c₁ _c₂ => throwError "NIY"

end
end Lean.Meta.Grind.Arith.Cutsat
