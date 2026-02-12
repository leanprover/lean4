/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

prelude
import Init.Data.BitVec
import Lean.SimpLC.Exceptions.Root
import Std.Tactic.BVDecide

set_option Elab.async false -- `simplc` crashes on the command line with a 139 without this.

simp_lc ignore BitVec.getLsbD_of_ge
simp_lc ignore BitVec.getMsbD_of_ge

namespace BitVec

-- This would be resolved by simply using `setWidth` instead of `cast`!
-- TODO: discuss with Tobias et al.
example (h : v = w) (x : BitVec v) : x.cast h = x.setWidth w := by
  ext
  simp_all
simp_lc allow BitVec.setWidth_eq BitVec.setWidth_cast

example (w : Nat) : 1#w = if w = 0 then 0#w else 1#w := by
  cases w <;> simp
simp_lc allow BitVec.udiv_one BitVec.udiv_self

-- This is commented out because `cadical` doesn't seem to be available in Nix CI.
-- example (x : BitVec 1) : x = if x = 0#1 then 0#1 else 1#1 := by bv_decide
simp_lc allow BitVec.udiv_eq_and BitVec.udiv_self

example (w : Nat) : w = 0 → 0#w = 1#w := by rintro rfl; simp
simp_lc allow BitVec.sdiv_self BitVec.sdiv_one

-- TODO: these need further investigation.
simp_lc allow BitVec.neg_mul BitVec.mul_twoPow_eq_shiftLeft
simp_lc allow BitVec.shiftLeft_eq_zero BitVec.shiftLeft_zero
simp_lc allow BitVec.lt_ofFin BitVec.not_allOnes_lt
simp_lc allow BitVec.lt_one_iff BitVec.ofFin_lt
simp_lc allow BitVec.lt_one_iff BitVec.not_allOnes_lt
simp_lc allow BitVec.ofFin_lt BitVec.not_lt_zero
simp_lc allow BitVec.ofNat_lt_ofNat BitVec.lt_one_iff
simp_lc allow BitVec.le_ofFin BitVec.allOnes_le_iff
simp_lc allow BitVec.le_zero_iff BitVec.allOnes_le_iff
simp_lc allow BitVec.ofFin_le BitVec.le_zero_iff
simp_lc allow BitVec.ofNat_le_ofNat BitVec.le_zero_iff
simp_lc allow BitVec.getMsbD_setWidth BitVec.getMsbD_setWidth_add

/-
The actual checks happen in `tests/lean/000_simplc.lean`.
This commented out command remains here for convenience while debugging.
-/
-- #guard_msgs (drop info) in
-- simp_lc check in BitVec
