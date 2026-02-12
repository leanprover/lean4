/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

prelude
import Init.Data.Sum
import Lean.SimpLC.Exceptions.List
import Lean.SimpLC.Exceptions.Bool
import Lean.SimpLC.Exceptions.Nat
import Lean.SimpLC.Exceptions.Root

set_option Elab.async false -- `simplc` crashes on the command line with a 139 without this.

simp_lc ignore Sum.getLeft_eq_iff
simp_lc ignore Sum.getRight_eq_iff

/-
The actual checks happen in `tests/lean/000_simplc.lean`.
This commented out command remains here for convenience while debugging.
-/
-- #guard_msgs (drop info) in
-- simp_lc check in Sum List Bool Nat _root_
