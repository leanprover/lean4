/-
Copyright (c) 2024 FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Lean.Elab.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Add
import Lean.Elab.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Append
import Lean.Elab.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Eq
import Lean.Elab.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Extract
import Lean.Elab.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.GetLsb
import Lean.Elab.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Mul
import Lean.Elab.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Not
import Lean.Elab.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Replicate
import Lean.Elab.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.RotateLeft
import Lean.Elab.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.RotateRight
import Lean.Elab.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.ShiftLeft
import Lean.Elab.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.ShiftRight
import Lean.Elab.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.SignExtend
import Lean.Elab.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Ult
import Lean.Elab.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.ZeroExtend

/-!
This directory contains the verification of bitblasters for all basic operations on `BVExpr` and
`BVPred`.
-/
