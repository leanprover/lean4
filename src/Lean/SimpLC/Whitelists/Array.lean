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
-- Hopefully resolved by https://github.com/leanprover/lean4/pull/5896
simp_lc whitelist Array.back_eq_back? List.back_toArray
-- Hopefully resolved by https://github.com/leanprover/lean4/pull/5895
simp_lc whitelist Array.beq_toList beq_self_eq_true
simp_lc whitelist BEq.refl Array.beq_toList
-- Hopefully resolved by https://github.com/leanprover/lean4/pull/5892
simp_lc whitelist forIn'_eq_forIn Array.forIn'_toList
simp_lc whitelist Array.forIn'_toList List.forIn'_eq_forIn

/-
The actual checks happen in `tests/lean/run/simplc.lean`.
This commented out command remains here for convenience while debugging.
-/
-- #guard_msgs (drop info) in
-- simp_lc check in Array List BEq Id _root_
