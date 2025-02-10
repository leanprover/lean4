/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
prelude
import Init.Data.Array
import Lean.SimpLC.Exceptions.Root
import Lean.SimpLC.Exceptions.List

-- These are facts about `Array Prop`, which hopefully never appear in the wild!
simp_lc allow dite_else_false Array.getD_eq_get?
simp_lc allow dite_else_true Array.getD_eq_get?

simp_lc ignore Array.getElem_mem -- Parallel to `List.getElem_mem`

-- These higher order simp lemmas cause many confluence problems. Reconsider?
simp_lc ignore Array.filterMap_subtype
simp_lc ignore Array.map_subtype
simp_lc ignore Array.foldl_subtype'
simp_lc ignore Array.foldr_subtype'
simp_lc ignore Array.foldlM_subtype
simp_lc ignore Array.foldrM_subtype
simp_lc ignore Array.mapFinIdx_eq_mapIdx
simp_lc ignore Array.findSome?_subtype
simp_lc ignore Array.findFinIdx?_subtype
simp_lc ignore Array.findIdx_subtype
simp_lc ignore Array.findIdx?_subtype

-- This would be confluent with `Array.foldlM_map`,
-- but that causes other problems (which we should document).
simp_lc allow List.forIn'_toArray Array.forIn'_yield_eq_foldlM
simp_lc allow Array.forIn_map Array.forIn_yield_eq_foldlM
simp_lc allow Array.forIn'_map Array.forIn'_yield_eq_foldlM -- this would also require commuting `map` and `attach`
-- This would be confluent with `Array.foldl_map`, but that can't be a simp lemma.
simp_lc allow List.forIn'_toArray Array.forIn'_yield_eq_foldl
simp_lc allow Array.forIn_map Array.forIn_yield_eq_foldl
simp_lc allow Array.forIn'_map Array.forIn'_yield_eq_foldl -- this would also require commuting `map` and `attach`

-- These would work except that `simp_all` is not willing to make a copy of the hypothesis.
simp_lc allow Array.getElem?_eq_getElem Array.getElem?_pmap
simp_lc allow Array.getElem?_eq_getElem Array.getElem?_map
simp_lc allow Array.getElem?_eq_getElem Array.getElem?_mapFinIdx
simp_lc allow Array.getElem?_eq_getElem Array.getElem?_attachWith
simp_lc allow Array.getElem?_eq_getElem Array.getElem?_attach
simp_lc allow Array.getElem?_mapIdx Array.getElem?_eq_getElem
simp_lc allow Array.getElem?_unattach Array.getElem?_eq_getElem

-- Fails at `⊢ decide (b ∈ l.push a) = (decide (b ∈ l) || b == a)`
-- because simp won't apply `Array.mem_push` inside `decide`.
simp_lc allow Array.contains_eq_mem Array.contains_push

-- Fails at `⊢ Array.filterMap ((some ∘ f) ∘ g) l = Array.map (f ∘ g) l`
-- and can't apply `Array.filterMap_eq_map` on the LHS because the associativity is wrong.
simp_lc allow Array.filterMap_map Array.filterMap_eq_map

-- Gets stuck with a hypothesis `h : a = b ∧ p a = true` and simp can't use it to apply `Array.filter_push_of_pos`.
simp_lc allow Array.filterMap_eq_filter Array.filterMap_push_some

namespace Option

@[simp] theorem isSome_guard {p} [DecidablePred p] {a : α} : (guard p a).isSome = decide (p a) := by
  simp only [guard]
  split <;> simp_all

@[simp] theorem get_guard {p} [DecidablePred p] {a : α} {h} : (guard p a).get h = a := by
  simp [guard]

end Option

-- Gets stuck at `⊢ Array.filter p (Array.map f l) 0 l.size = Array.filterMap ((Option.guard fun x => p x = true) ∘ f) l`.
-- Not certain what to hope for here. Having `Function.comp_def` in the simp set would probably resolve it.
simp_lc allow Array.filterMap_eq_filter Array.filterMap_map

-- The simp normal form for `filterMap` vs `filter`+`map` still needs work.
simp_lc allow Array.filterMap_eq_filter Array.filterMap_attachWith

-- The simp normal form for `attachWith` vs `map`+`attach` still needs work.
simp_lc allow Array.filterMap_some Array.filterMap_attachWith

namespace List

@[simp] theorem foldl_nat_add {f : α → Nat} {n : Nat} {l : List α} :
    l.foldl (fun x y => x + f y) n = n + (l.map f).sum := by
  induction l generalizing n <;> simp_all [Nat.add_assoc]

@[simp] theorem foldr_nat_add {f : α → Nat} {n : Nat} {l : List α} :
    l.foldr (fun x y => y + f x) n = n + (l.map f).sum := by
  induction l generalizing n <;> simp_all [Nat.add_assoc, Nat.add_comm (f _)]

@[simp] theorem sum_map_nat_const_mul {f : α → Nat} {b : Nat} {l : List α} :
    (l.map (fun a => b * f a)).sum  = b * (l.map f).sum := by
  induction l <;> simp_all [Nat.mul_add]

@[simp] theorem sum_map_mul_nat_const {f : α → Nat} {b : Nat} {l : List α} :
    (l.map (fun a => f a * b)).sum = (l.map f).sum * b := by
  induction l <;> simp_all [Nat.add_mul]

end List

namespace Array

@[simp] theorem foldl_nat_add {f : α → Nat} {n : Nat} {l : Array α} :
    l.foldl (fun x y => x + f y) n = n + (l.map f).sum := by
  cases l
  simp

@[simp] theorem foldr_nat_add {f : α → Nat} {n : Nat} {l : Array α} :
    l.foldr (fun x y => y + f x) n = n + (l.map f).sum := by
  cases l
  simp

@[simp] theorem sum_map_nat_const_mul {f : α → Nat} {b : Nat} {l : Array α} :
    (l.map (fun a => b * f a)).sum  = b * (l.map f).sum := by
  cases l
  simp_all [Nat.mul_add]

@[simp] theorem sum_map_mul_nat_const {f : α → Nat} {b : Nat} {l : Array α} :
    (l.map (fun a => f a * b)).sum = (l.map f).sum * b := by
  cases l
  simp_all [Nat.add_mul]

end Array

-- Just missing some arithmetic.
simp_lc allow Array.foldl_append' Array.foldl_add_const
simp_lc allow Array.foldr_push' Array.foldr_add_const
simp_lc allow Array.foldr_append' Array.foldr_add_const
simp_lc allow Array.findSome?_mkArray_of_pos Array.findSome?_mkArray_of_isSome

attribute [simp] List.findSome?_append Array.findSome?_append

attribute [simp] Option.or_of_isSome Option.or_of_isNone

attribute [simp] List.reverse_flatten Array.reverse_flatten Vector.reverse_flatten

-- Gets stuck at `List.foldlM ⋯ as.toList.attach`. Since we push `toList` inwards, it's not clear what to do,
-- except add an extra lemma.
simp_lc allow List.forIn'_yield_eq_foldlM Array.forIn'_toList
-- Gets stuck at `List.foldl ⋯ as.toList.attach`
simp_lc allow Array.forIn'_toList List.forIn'_yield_eq_foldl

-- `⊢ (Array.map (fun x => mkArray x.size b) L).flatten = mkArray (Array.map Array.size L).sum b`
-- Sufficiently obscure that it doesn't need a lemma.
simp_lc allow Array.map_flatten Array.map_const



namespace Array

theorem push_mkArray {n : Nat} {a : α} : (mkArray n a).push a = mkArray (n + 1) a := by
  rw [mkArray_succ]

@[simp] theorem pop_mkArray {n : Nat} {a : α} : (mkArray n a).pop = mkArray (n - 1) a := by
  rw [← List.toArray_replicate, List.pop_toArray]
  simp

end Array

namespace Vector

@[simp] theorem pop_mkVector {n : Nat} {a : α} : (mkVector n a).pop = mkVector (n - 1) a := by
  rw [mkVector_eq_mk_mkArray, pop_mk]
  simp

end Vector

namespace Array

-- Ideally this would never appear, as we push `toList` inwards and `toArray` outwards.
-- It sometimes appears in confluence problems, so we just add it to the simp set.
@[simp] theorem toArray_reverse_toList {xs: Array α} : xs.toList.reverse.toArray = xs.reverse := by
  cases xs
  simp

end Array

simp_lc inspect List.foldr_cons_eq_append' Array.foldr_toList

-- We currently have `Array.flatten_toArray_map`, `Array.flatten_toArray`, `List.flatten_toArray`, and `Array.flatten_toArray_map_toArray`!
-- All but the second are simp lemmas, but the second really should be!
simp_lc inspect Array.flatMap_toArray Array.flatMap_id'
simp_lc inspect Array.flatMap_toArray Array.flatMap_id
simp_lc inspect Array.flatMap_id' List.flatMap_toArray
simp_lc inspect Array.flatMap_id List.flatMap_toArray

simp_lc inspect Array.pmap_eq_map Array.pmap_attachWith
simp_lc inspect Array.pmap_eq_attachWith Array.pmap_attachWith
simp_lc inspect Array.pmap_attach Array.pmap_eq_map
simp_lc inspect Array.pmap_attach Array.pmap_eq_attachWith

-- ```
-- al : a ∈ l
-- pa : p a = true
-- ⊢ l.size - 1 = (l.eraseP p).size
-- ```
simp_lc inspect Array.size_eraseP_of_mem Array.length_toList
simp_lc inspect Array.size_toArray List.length_eraseP_of_mem

simp_lc inspect Array.size_toArray Array.size_eraseIdx


attribute [simp] Array.getElem_append_left Array.getElem_append_right

/-
The actual checks happen in `tests/lean/000_simplc.lean`.
This commented out command remains here for convenience while debugging.
-/
#guard_msgs (drop info) in
simp_lc check in Array List BEq Id _root_
