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

export Int.Linear (Var Poly RelCnstr DvdCnstr)

-- TODO: include RelCnstrWithProof and RelCnstrProof
mutual
/-- A divisibility constraint and its justification/proof. -/
structure DvdCnstrWithProof where
  c  : DvdCnstr
  h  : DvdCnstrProof
  /-- Unique id for caching proofs in `ProofM` -/
  id : Nat

inductive DvdCnstrProof where
  | expr (h : Expr)
  | norm (c : DvdCnstrWithProof)
  | divCoeffs (c : DvdCnstrWithProof)
  | solveCombine (c₁ c₂ : DvdCnstrWithProof)
  | solveElim (c₁ c₂ : DvdCnstrWithProof)

structure RelCnstrWithProof where
  c  : RelCnstr
  h  : RelCnstrProof
  id : Nat

inductive RelCnstrProof where
  | expr (h : Expr)
  | notExpr (c : Expr)
  | norm (c : RelCnstrWithProof)
  | divCoeffs (c : RelCnstrWithProof)
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
  dvdCnstrs : PArray (Option DvdCnstrWithProof) := {}
  /--
  Mapping from variables to their "lower" bounds. We say a relational constraint `c` is a lower bound for a variable `x`
  if `x` is the maximal variable in `c`, `c.isLe`, and `x` coefficient in `c` is negative.
  -/
  lowers : PArray (PArray RelCnstrWithProof) := {}
  /--
  Mapping from variables to their "upper" bounds. We say a relational constraint `c` is a upper bound for a variable `x`
  if `x` is the maximal variable in `c`, `c.isLe`, and `x` coefficient in `c` is positive.
  -/
  uppers : PArray (PArray RelCnstrWithProof) := {}
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
