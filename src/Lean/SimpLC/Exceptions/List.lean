/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

prelude
import Init.Data.List
import Init.Omega
import Lean.SimpLC.Exceptions.Root

set_option Elab.async false -- `simplc` crashes on the command line with a 139 without this.

open List

simp_lc allow List.map_const List.map_flatten -- too hard?

simp_lc allow List.drop_tail List.drop_one -- Would require an infinite chain of lemmas to resolve!
simp_lc allow List.findSome?_replicate_of_pos List.findSome?_replicate_of_isSome -- split in the discharger would get us there

-- These would all be okay, except that `simp_all` is unwilling to make a copy of a hypothesis which is being used.
simp_lc allow List.getElem?_eq_getElem List.getElem?_zipIdx
simp_lc allow List.getElem?_map List.getElem?_eq_getElem
simp_lc allow List.getElem?_modify_eq List.getElem?_eq_getElem
simp_lc allow List.getElem?_mapIdx List.getElem?_eq_getElem
simp_lc allow List.getElem?_eq_getElem List.getElem?_modifyHead_zero

simp_lc allow List.drop_one List.drop_left' -- `h : l₁.length = 1 ⊢ (l₁ ++ l₂).tail = l₂`

-- These would be resolved by a `ring` tactic, but are beyond `simp +arith`.
simp_lc allow List.foldl_cons List.foldl_add_const
simp_lc allow List.foldr_cons List.foldr_add_const
simp_lc allow List.foldr_append List.foldr_add_const
simp_lc allow List.foldl_append List.foldl_add_const

/-- This would require an infinite chain of lemmas. -/
example {a : α} {l₁ l₂ : List α} : ¬ a :: (l₁ ++ l₂) <+ l₁ := by
  intro h
  replace h := h.length_le
  simp at h
  omega
simp_lc allow List.Sublist.cons List.append_right_sublist_self

/-- This would require an infinite chain of lemmas. -/
example {a : α} {l₁ l₂ : List α} : ¬ l₁ ++ (a :: l₂) <+ l₂ := by
  intro h
  replace h := h.length_le
  simp at h
  omega
simp_lc allow List.append_left_sublist_self List.Sublist.cons

/- The four can't be easily handled by `simp` without introducing infinite chains of lemmas,
but would be nice to have good automation for! -/
simp_lc allow List.cons_sublist_cons List.Sublist.cons
simp_lc allow List.append_left_sublist_self List.sublist_append_of_sublist_left
simp_lc allow List.append_left_sublist_self List.sublist_append_of_sublist_right
simp_lc allow List.append_right_sublist_self List.sublist_append_of_sublist_right
simp_lc allow List.append_sublist_append_left List.sublist_append_of_sublist_right
simp_lc allow List.append_sublist_append_right List.sublist_append_of_sublist_left

-- This one works, just not by `simp_all` because it is unwilling to make a copy of `h₂`.
example {p : α → Prop} {f : (a : α) → p a → β} {l : List α} {h₁ : ∀ (a : α), a ∈ l → p a}
    {n : Nat} {h₂ : n < (List.pmap f l h₁).length} :
    some (f (l[n]'(by simpa using h₂)) (h₁ _ (getElem_mem _))) =
      Option.pmap f l[n]? (fun a h => h₁ a (mem_of_getElem? h)) := by
  simp at h₂
  simp [h₂]

simp_lc allow List.getElem?_eq_getElem List.getElem?_pmap
-- As above, `simp_all` is unwilling to make a copy of a hypothesis.
simp_lc allow List.getElem?_eq_getElem List.getElem?_attach
simp_lc allow List.getElem?_eq_getElem List.getElem?_attachWith
simp_lc allow List.getElem?_eq_getElem List.getElem?_mapFinIdx
simp_lc allow List.getElem?_eq_getElem List.getElem?_unattach

-- These are helpful for `simp` to discharge side conditions, but generate too many false positives.
simp_lc ignore List.head_mem
simp_lc ignore List.getLast_mem
simp_lc ignore List.getElem_mem

-- These higher order simp lemmas cause many confluence problems. Reconsider?
simp_lc ignore List.filterMap_subtype
simp_lc ignore List.map_subtype
simp_lc ignore List.flatMap_subtype
simp_lc ignore List.foldl_subtype
simp_lc ignore List.foldr_subtype
simp_lc ignore List.foldlM_subtype
simp_lc ignore List.foldrM_subtype
simp_lc ignore List.mapFinIdx_eq_mapIdx
simp_lc ignore List.findSome?_subtype
simp_lc ignore List.findFinIdx?_subtype
simp_lc ignore List.findIdx_subtype
simp_lc ignore List.findIdx?_subtype

/-
The actual checks happen in `tests/lean/000_simplc.lean`.
This commented out command remains here for convenience while debugging.
-/
#guard_msgs (drop info) in

-- This would be confluent with `List.foldlM_map`,
-- but that causes other problems (which we should document).
simp_lc allow List.forIn'_yield_eq_foldlM List.forIn'_map
simp_lc allow List.forIn'_yield_eq_foldlM List.forIn'_cons
simp_lc allow List.idRun_forIn_yield_eq_foldl List.forIn_map
-- This would be confluent with `List.foldl_map`, but that can't be a simp lemma.
simp_lc allow List.forIn'_map List.idRun_forIn'_yield_eq_foldl
simp_lc allow List.forIn'_cons List.idRun_forIn'_yield_eq_foldl
simp_lc allow List.forIn_yield_eq_foldlM List.forIn_map

namespace List

-- `foldl_push_eq_append` and `foldr_push_eq_append` are now in Init.Data.Array.Lemmas

@[simp] theorem tail_take_one {l : List α} : (l.take 1).tail = [] := by
  induction l <;> simp [*]

-- `getElem_append_left` and `getElem_append_right` are already `@[simp]` in Init.Data.List.BasicAux

end List

-- We should try adding:
-- attribute [simp] List.map_attach
-- `List.foldr_push` and `List.foldl_push` no longer exist
simp_lc allow List.foldr_push_eq_append List.foldr_attachWith
simp_lc allow List.foldl_push_eq_append List.foldl_attachWith

-- FIXME These still need thinking about.
simp_lc allow List.pmap_eq_attachWith List.pmap_attachWith
simp_lc allow List.pmap_eq_attachWith List.pmap_attach
simp_lc allow List.pmap_attachWith List.pmap_eq_map
simp_lc allow List.pmap_attach List.pmap_eq_map
simp_lc allow List.attachWith_mem_toArray List.attachWith_reverse
simp_lc allow List.attachWith_mem_toArray List.attachWith_append
simp_lc allow List.attachWith_cons List.attachWith_mem_toArray
simp_lc allow List.map_const List.map_attachWith
simp_lc allow List.foldr_cons_eq_append' List.foldr_attachWith

-- FIXME what is happening here?
simp_lc allow List.size_toArray List.length_eraseP_of_mem

namespace List

@[simp] theorem flatten_map_flatten_map {xss : List (List α)} {f : α → List β} :
    (List.map (fun xs => (List.map f xs).flatten) xss).flatten =
      (xss.map (fun xs => xs.map f)).flatten.flatten := by
  induction xss with
  | nil => simp
  | cons head tail ih => simp [ih]

@[simp] theorem nat_sum_append {l₁ l₂ : List Nat} : (l₁ ++ l₂).sum = l₁.sum + l₂.sum := by
  induction l₁ with
  | nil => simp
  | cons head tail ih => simp [ih]; omega

@[simp] theorem nat_sum_map_nat_sum_map {xss : List (List α)} {f : α → Nat} :
    (xss.map (fun y => (y.map f).sum)).sum = (xss.map (fun y => y.map f)).flatten.sum := by
  induction xss with
  | nil => simp
  | cons head tail ih => simp_all [Function.comp_def]

@[simp] theorem sum_map_toList [Zero β] [Add β] {xs : Array α} {f : α → β} :
    (xs.toList.map f).sum = (xs.map f).sum := by
  rcases xs with ⟨xs⟩
  induction xs with
  | nil => simp
  | cons head tail ih => simp

@[simp] theorem nat_sum_reverse {l : List Nat} : l.reverse.sum = l.sum := by
  induction l with
  | nil => simp
  | cons head tail ih => simp [ih]; omega

end List

/-
The actual checks happen in `tests/lean/000_simplc.lean`.
This commented out command remains here for convenience while debugging.
-/
-- #guard_msgs (drop info) in
-- simp_lc check in List BEq _root_
