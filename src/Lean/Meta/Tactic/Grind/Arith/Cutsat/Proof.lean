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
  | .ofEq x c =>
    return mkApp7 (mkConst ``Int.Linear.dvd_of_eq)
      (← getContext) (toExpr x) (toExpr c.p) (toExpr c'.d) (toExpr c'.p)
      reflBoolTrue (← c.toExprProof)
  | .subst x c₁ c₂ =>
    return mkApp10 (mkConst ``Int.Linear.eq_dvd_subst)
      (← getContext) (toExpr x) (toExpr c₁.p) (toExpr c₂.d) (toExpr c₂.p) (toExpr c'.d) (toExpr c'.p)
      reflBoolTrue (← c₁.toExprProof) (← c₂.toExprProof)

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
  | .subst x c₁ c₂ =>
    let a := c₁.p.coeff x
    let thm := if a ≥ 0 then
      mkConst ``Int.Linear.eq_le_subst_nonneg
    else
      mkConst ``Int.Linear.eq_le_subst_nonpos
    return mkApp8 thm
        (← getContext) (toExpr x) (toExpr c₁.p) (toExpr c₂.p) (toExpr c'.p)
        reflBoolTrue
        (← c₁.toExprProof) (← c₂.toExprProof)

partial def EqCnstr.toExprProof (c' : EqCnstr) : ProofM Expr := c'.caching do
  match c'.h with
  | .expr h =>
    return h
  | .core p₁ p₂ h =>
    return mkApp6 (mkConst ``Int.Linear.eq_of_core) (← getContext) (toExpr p₁) (toExpr p₂) (toExpr c'.p) reflBoolTrue h
  | .norm c =>
    return mkApp5 (mkConst ``Int.Linear.eq_norm) (← getContext) (toExpr c.p) (toExpr c'.p) reflBoolTrue (← c.toExprProof)
  | .divCoeffs c =>
    let k := c.p.gcdCoeffs c.p.getConst
    return mkApp6 (mkConst ``Int.Linear.eq_coeff) (← getContext) (toExpr c.p) (toExpr c'.p) (toExpr k) reflBoolTrue (← c.toExprProof)
  | .subst x c₁ c₂  =>
    return mkApp8 (mkConst ``Int.Linear.eq_eq_subst)
      (← getContext) (toExpr x) (toExpr c₁.p) (toExpr c₂.p) (toExpr c'.p)
      reflBoolTrue (← c₁.toExprProof) (← c₂.toExprProof)

end

def setInconsistent (h : UnsatProof) : GoalM Unit := do
  let hf ← withProofContext do
    match h with
    | .le c =>
      trace[grind.cutsat.le.unsat] "{← c.pp}"
      return mkApp4 (mkConst ``Int.Linear.le_unsat) (← getContext) (toExpr c.p) reflBoolTrue (← c.toExprProof)
    | .dvd c =>
      trace[grind.cutsat.dvd.unsat] "{← c.pp}"
      return mkApp5 (mkConst ``Int.Linear.dvd_unsat) (← getContext) (toExpr c.d) (toExpr c.p) reflBoolTrue (← c.toExprProof)
    | .eq c =>
      trace[grind.cutsat.eq.unsat] "{← c.pp}"
      if c.p.isUnsatEq then
        return mkApp4 (mkConst ``Int.Linear.eq_unsat) (← getContext) (toExpr c.p) reflBoolTrue (← c.toExprProof)
      else
        let k := c.p.gcdCoeffs'
        return mkApp5 (mkConst ``Int.Linear.eq_unsat_coeff) (← getContext) (toExpr c.p) (toExpr (Int.ofNat k)) reflBoolTrue (← c.toExprProof)
  closeGoal hf

end Lean.Meta.Grind.Arith.Cutsat
