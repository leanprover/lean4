/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Lean.SimpLC.Whitelists.Root
import Lean.SimpLC.Whitelists.List

-- These are facts about `Array Prop`, which hopefully never appear in the wild!
simp_lc whitelist dite_else_false Array.getD_eq_get?
simp_lc whitelist dite_else_true Array.getD_eq_get?

-- TODO: fixable, with a more general `Array.foldr_push'` simp lemma.
simp_lc whitelist Array.foldr_push' Array.foldr_subtype'

-- TODO: move to library
@[simp] theorem List.mapM_id {l : List α} {f : α → Id β} : l.mapM f = l.map f := by
  induction l <;> simp_all

-- TODO: move to library
@[simp] theorem Array.mapM_id {l : Array α} {f : α → Id β} : l.mapM f = l.map f := by
  induction l <;> simp_all

simp_lc ignore Array.getElem_mem -- Parallel to `List.getElem_mem`

-- These higher order simp lemmas cause many confluence problems. Reconsider?
simp_lc ignore Array.filterMap_subtype
simp_lc ignore Array.map_subtype
simp_lc ignore Array.foldl_subtype
simp_lc ignore Array.foldr_subtype

-- TODO: re-evaluate these (appeared while moving `SimpLC` into Lean.)
simp_lc whitelist Array.isEmpty.eq_1 List.isEmpty_toArray

/-
The actual checks happen in `tests/lean/run/simplc.lean`.
This commented out command remains here for convenience while debugging.
-/
-- #guard_msgs (drop info) in
-- simp_lc check in Array List BEq Id _root_
