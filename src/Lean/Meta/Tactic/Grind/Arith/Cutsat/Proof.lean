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
  | .ofLeGe c₁ c₂ =>
    return mkApp6 (mkConst ``Int.Linear.eq_of_le_ge)
      (← getContext) (toExpr c₁.p) (toExpr c₂.p)
      reflBoolTrue (← c₁.toExprProof) (← c₂.toExprProof)

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
  | .ofLeDiseq c₁ c₂ =>
    return mkApp7 (mkConst ``Int.Linear.le_of_le_diseq)
      (← getContext) (toExpr c₁.p) (toExpr c₂.p) (toExpr c'.p)
      reflBoolTrue (← c₁.toExprProof) (← c₂.toExprProof)
  | .ofDiseqSplit c₁ fvarId h _ =>
    let p₂ := c₁.p.addConst 1
    let hFalse ← h.toExprProofCore
    let hNot := mkLambda `h .default (mkIntLE (← p₂.denoteExpr') (mkIntLit 0)) (hFalse.abstract #[mkFVar fvarId])
    return mkApp7 (mkConst ``Int.Linear.diseq_unsat_split)
      (← getContext) (toExpr c₁.p) (toExpr p₂) (toExpr c'.p) reflBoolTrue (← c₁.toExprProof) hNot

partial def DiseqCnstr.toExprProof (c' : DiseqCnstr) : ProofM Expr := c'.caching do
  match c'.h with
  | .expr h =>
    return h
  | .core p₁ p₂ h =>
    return mkApp6 (mkConst ``Int.Linear.diseq_of_core) (← getContext) (toExpr p₁) (toExpr p₂) (toExpr c'.p) reflBoolTrue h
  | .norm c =>
    return mkApp5 (mkConst ``Int.Linear.diseq_norm) (← getContext) (toExpr c.p) (toExpr c'.p) reflBoolTrue (← c.toExprProof)
  | .divCoeffs c =>
    let k := c.p.gcdCoeffs c.p.getConst
    return mkApp6 (mkConst ``Int.Linear.diseq_coeff) (← getContext) (toExpr c.p) (toExpr c'.p) (toExpr k) reflBoolTrue (← c.toExprProof)
  | .neg c =>
    return mkApp5 (mkConst ``Int.Linear.diseq_neg) (← getContext) (toExpr c.p) (toExpr c'.p) reflBoolTrue (← c.toExprProof)
  | .subst x c₁ c₂  =>
    return mkApp8 (mkConst ``Int.Linear.eq_diseq_subst)
      (← getContext) (toExpr x) (toExpr c₁.p) (toExpr c₂.p) (toExpr c'.p)
      reflBoolTrue (← c₁.toExprProof) (← c₂.toExprProof)

partial def UnsatProof.toExprProofCore (h : UnsatProof) : ProofM Expr := do
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
  | .diseq c =>
    trace[grind.cutsat.diseq.unsat] "{← c.pp}"
    return mkApp4 (mkConst ``Int.Linear.diseq_unsat) (← getContext) (toExpr c.p) reflBoolTrue (← c.toExprProof)

end

def UnsatProof.toExprProof (h : UnsatProof) : GoalM Expr := do
  withProofContext do h.toExprProofCore

def setInconsistent (h : UnsatProof) : GoalM Unit := do
  if (← get').caseSplits then
    -- Let the search procedure in `SearchM` resolve the conflict.
    modify' fun s => { s with conflict? := some h }
  else
    let h ← h.toExprProof
    closeGoal h

/-!
A cutsat proof may depend on decision variables.
We collect them and perform non chronological backtracking.
-/

structure CollectDecVars.State where
  visited : Std.HashSet Nat := {}
  found : FVarIdSet := {}

abbrev CollectDecVarsM := ReaderT FVarIdSet (StateM CollectDecVars.State)

private def alreadyVisited (id : Nat) : CollectDecVarsM Bool := do
  if (← get).visited.contains id then return true
  modify fun s => { s with visited := s.visited.insert id }
  return false

private def markAsFound (fvarId : FVarId) : CollectDecVarsM Unit := do
  modify fun s => { s with found := s.found.insert fvarId }

private def collectExpr (e : Expr) : CollectDecVarsM Unit := do
  let .fvar fvarId := e | return ()
  if (← read).contains fvarId then
    markAsFound fvarId

mutual
partial def EqCnstr.collectDecVars (c' : EqCnstr) : CollectDecVarsM Unit := do unless (← alreadyVisited c'.id) do
  match c'.h with
  | .expr h => collectExpr h
  | .core .. => return () -- Equalities coming from the core never contain cutsat decision variables
  | .norm c | .divCoeffs c => c.collectDecVars
  | .subst _ c₁ c₂ | .ofLeGe c₁ c₂ => c₁.collectDecVars; c₂.collectDecVars

partial def DvdCnstr.collectDecVars (c' : DvdCnstr) : CollectDecVarsM Unit := do unless (← alreadyVisited c'.id) do
  match c'.h with
  | .expr h => collectExpr h
  | .norm c | .elim c | .divCoeffs c | .ofEq _ c => c.collectDecVars
  | .solveCombine c₁ c₂ | .solveElim c₁ c₂ | .subst _ c₁ c₂ => c₁.collectDecVars; c₂.collectDecVars

partial def LeCnstr.collectDecVars (c' : LeCnstr) : CollectDecVarsM Unit := do unless (← alreadyVisited c'.id) do
  match c'.h with
  | .expr h => collectExpr h
  | .notExpr .. => return () -- This kind of proof is used for connecting with the `grind` core.
  | .norm c | .divCoeffs c => c.collectDecVars
  | .combine c₁ c₂ | .subst _ c₁ c₂ | .ofLeDiseq c₁ c₂ => c₁.collectDecVars; c₂.collectDecVars
  | .ofDiseqSplit _ _ _ decVars =>
    -- Recall that we cache the decision variables used in this kind of proof
    for fvar in decVars do
      markAsFound fvar

partial def DiseqCnstr.collectDecVars (c' : DiseqCnstr) : CollectDecVarsM Unit := do unless (← alreadyVisited c'.id) do
  match c'.h with
  | .expr h => collectExpr h
  | .core .. => return () -- Disequalities coming from the core never contain cutsat decision variables
  | .norm c | .divCoeffs c | .neg c => c.collectDecVars
  | .subst _ c₁ c₂  => c₁.collectDecVars; c₂.collectDecVars

end

def UnsatProof.collectDecVars (h : UnsatProof) : CollectDecVarsM Unit := do
  match h with
  | .le c | .dvd c | .eq c | .diseq c => c.collectDecVars

abbrev CollectDecVarsM.run (x : CollectDecVarsM Unit) (decVars : FVarIdSet) : FVarIdSet :=
  let (_, s) := x decVars |>.run {}
  s.found

end Lean.Meta.Grind.Arith.Cutsat
