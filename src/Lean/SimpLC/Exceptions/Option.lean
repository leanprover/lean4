/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

prelude
import Init.Data.Option
import Lean.SimpLC.Exceptions.Root

set_option Elab.async false -- `simplc` crashes on the command line with a 139 without this.

-- These higher order simp lemmas cause many confluence problems. Reconsider?
simp_lc ignore Option.map_subtype
simp_lc ignore Option.bind_subtype

namespace Option

-- `not_mem_none` is already `@[simp]` in Init.Data.Option.Lemmas

@[simp] theorem elim_map {f : α → β} {o : Option α} {b : γ} {g} :
    (Option.map f o).elim b g = o.elim b (fun a => g (f a)) := by
  cases o <;> simp


@[simp] theorem pelim_map {f : α → β} {o : Option α} {b : γ} {g} :
    (Option.map f o).pelim b g = o.pelim b (fun a h => g (f a) (mem_map_of_mem f h)) := by
  cases o <;> simp

/-
The actual checks happen in `tests/lean/000_simplc.lean`.
This commented out command remains here for convenience while debugging.
-/
-- #guard_msgs (drop info) in
-- simp_lc check in Option _root_
