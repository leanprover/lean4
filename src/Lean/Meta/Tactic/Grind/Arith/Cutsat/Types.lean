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
  c : DvdCnstr
  h : DvdCnstrProof

inductive DvdCnstrProof where
  | expr (h : Expr)
  | norm (c : DvdCnstrWithProof)
  | divCoeffs (c : DvdCnstrWithProof)
  | solveCombine (c₁ c₂ : DvdCnstrWithProof)
  | solveElim (c₁ c₂ : DvdCnstrWithProof)
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
  deriving Inhabited

end Lean.Meta.Grind.Arith.Cutsat
