/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Data.Int.Linear
import Lean.Data.PersistentArray
import Lean.Meta.Tactic.Grind.ENodeKey
import Lean.Meta.Tactic.Grind.Arith.Util

namespace Lean.Meta.Grind.Arith.Cutsat

export Int.Linear (Var Poly)

mutual
/-- A divisibility constraint and its justification/proof. -/
structure DvdCnstr where
  d  : Int
  p  : Poly
  h  : DvdCnstrProof
  /-- Unique id for caching proofs in `ProofM` -/
  id : Nat

inductive DvdCnstrProof where
  | expr (h : Expr)
  | norm (c : DvdCnstr)
  | divCoeffs (c : DvdCnstr)
  | solveCombine (c₁ c₂ : DvdCnstr)
  | solveElim (c₁ c₂ : DvdCnstr)
  | elim (c : DvdCnstr)

structure LeCnstr where
  p  : Poly
  h  : LeCnstrProof
  id : Nat

inductive LeCnstrProof where
  | expr (h : Expr)
  | notExpr (p : Poly) (h : Expr)
  | norm (c : LeCnstr)
  | divCoeffs (c : LeCnstr)
  | combine (c₁ c₂ : LeCnstr)
  -- TODO: missing constructors
end

/-- State of the cutsat procedure. -/
structure State where
  /-- Mapping from variables to their denotations. -/
  vars : PArray Expr := {}
  /-- Mapping from `Expr` to a variable representing it. -/
  varMap  : PHashMap ENodeKey Var := {}
  /--
  Mapping from variables to divisibility constraints. Recall that we keep the divisibility constraint in solved form.
  Thus, we have at most one divisibility per variable. -/
  dvdCnstrs : PArray (Option DvdCnstr) := {}
  /--
  Mapping from variables to their "lower" bounds. We say a relational constraint `c` is a lower bound for a variable `x`
  if `x` is the maximal variable in `c`, `c.isLe`, and `x` coefficient in `c` is negative.
  -/
  lowers : PArray (PArray LeCnstr) := {}
  /--
  Mapping from variables to their "upper" bounds. We say a relational constraint `c` is a upper bound for a variable `x`
  if `x` is the maximal variable in `c`, `c.isLe`, and `x` coefficient in `c` is positive.
  -/
  uppers : PArray (PArray LeCnstr) := {}
  /-- Partial assignment being constructed by cutsat. -/
  assignment : PArray Int := {}
  /-- Next unique id for a constraint. -/
  nextCnstrId : Nat := 0
  /-
  TODO: support for storing
  - Disjuctions: they come from conflict resolution, and disequalities.
  - Disequalities.
  - Linear integer terms appearing in the main module, and model-based equality propagation.
  -/
  deriving Inhabited

end Lean.Meta.Grind.Arith.Cutsat
