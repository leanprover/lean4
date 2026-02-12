/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

prelude
import Init.Data.Fin
import Init.Omega
import Lean.SimpLC

set_option Elab.async false -- `simplc` crashes on the command line with a 139 without this.

-- This seems like a weird corner case. The discharger doesn't simplify `h` because it is used.
example (n m : Nat) (i : Fin n) (h : 0 + n = m + n) : Fin.natAdd m i = Fin.cast (by omega) i := by
  simp at h
  ext
  simpa
simp_lc allow Fin.cast_addNat_right Fin.cast_addNat_zero

/-
The actual checks happen in `tests/lean/000_simplc.lean`.
This commented out command remains here for convenience while debugging.
-/
-- #guard_msgs (drop info) in
-- simp_lc check in Fin
