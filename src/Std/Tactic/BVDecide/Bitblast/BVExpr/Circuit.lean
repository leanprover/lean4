/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas

@[expose] public section

/-!
This directory contains the implementation and verification of the bitblaster for `BitVec` problems
with boolean substructure. For any primitive operation defined in `Basic` there does exist one
file in `Impl`, containing the bitblaster and one file in `Lemmas`, demonstrating that the circuit
produced by the bitblaster is correct.
-/
