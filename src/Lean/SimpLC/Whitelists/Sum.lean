/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
prelude
import Lean.SimpLC.Whitelists.List
import Lean.SimpLC.Whitelists.Bool
import Lean.SimpLC.Whitelists.Nat

-- Can we remove this globally?
attribute [-simp] Sum.exists Sum.forall

simp_lc ignore Sum.getLeft_eq_iff
simp_lc ignore Sum.getRight_eq_iff

/-
The actual checks happen in `tests/lean/run/simplc.lean`.
This commented out command remains here for convenience while debugging.
-/
-- #guard_msgs (drop info) in
-- simp_lc check in Sum List Bool Nat _root_
