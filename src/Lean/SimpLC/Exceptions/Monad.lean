/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
prelude
import Init.Control
import Lean.SimpLC.Exceptions.Root

set_option Elab.async false -- `simplc` crashes on the command line with a 139 without this.

/-
The actual checks happen in `tests/lean/000_simplc.lean`.
This commented out command remains here for convenience while debugging.
-/
-- #guard_msgs (drop info) in
-- simp_lc check in Monad LawfulMonad LawfulApplicative _root_ ExceptT
