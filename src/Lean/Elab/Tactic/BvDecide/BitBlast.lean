/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Lean.Elab.Tactic.BvDecide.BitBlast.BoolExpr
import Lean.Elab.Tactic.BvDecide.BitBlast.BVExpr

/-!
This directory contains the implementation of the bitblaster itself. It is split up into two parts:
1. Bitblasting of generic boolean substructures for SMT-like problems in `BoolExpr`.
2. The specific bitblaster for `BitVec` problems with boolean substructure in `BVExpr`.
-/
