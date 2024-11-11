/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
prelude
import Init.Data.Array
import Lean.SimpLC.Whitelists.Root
import Lean.SimpLC.Whitelists.List

-- These are facts about `Array Prop`, which hopefully never appear in the wild!
simp_lc whitelist dite_else_false Array.getD_eq_get?
simp_lc whitelist dite_else_true Array.getD_eq_get?

simp_lc ignore Array.getElem_mem -- Parallel to `List.getElem_mem`

-- These higher order simp lemmas cause many confluence problems. Reconsider?
simp_lc ignore Array.filterMap_subtype
simp_lc ignore Array.map_subtype
simp_lc ignore Array.foldl_subtype
simp_lc ignore Array.foldr_subtype

-- Surely this should work just by `simp`, without needing `cases`?
-- But I can't make it happen.
example {α : Type _} {l : List α} : decide (l.toArray.size = 0) = l.isEmpty := by
  cases l <;> simp
simp_lc whitelist Array.isEmpty.eq_1 List.isEmpty_toArray

/-
The actual checks happen in `tests/lean/000_simplc.lean`.
This commented out command remains here for convenience while debugging.
-/
-- #guard_msgs (drop info) in
-- simp_lc check in Array List BEq Id _root_
