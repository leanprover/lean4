/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
prelude
import Init.Control
import Lean.SimpLC.Exceptions.Root

-- TODO: move this to the library?
/--
This is just a duplicate of `LawfulApplicative.map_pure`,
but sometimes applies when that doesn't.
-/
@[simp] theorem LawfulMonad.map_pure' [Monad m] [LawfulMonad m] {a : α} :
    (f <$> pure a : m β) = pure (f a) := by simp

-- I can't work out why this isn't closed by `Functor.map_map`.
simp_lc allow LawfulMonad.bind_pure_comp bind_map_left

/-
The actual checks happen in `tests/lean/000_simplc.lean`.
This commented out command remains here for convenience while debugging.
-/
-- #guard_msgs (drop info) in
-- simp_lc check in Monad LawfulMonad LawfulApplicative _root_ ExceptT
