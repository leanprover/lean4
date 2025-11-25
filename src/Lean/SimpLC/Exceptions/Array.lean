/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

prelude
import Init.Data.Array
import Lean.SimpLC.Exceptions.Root
import Lean.SimpLC.Exceptions.List

set_option Elab.async false -- `simplc` crashes on the command line with a 139 without this.

simp_lc ignore Array.getElem_mem -- Parallel to `List.getElem_mem`
simp_lc ignore Array.back_mem

-- Confluence problems involving `Array Prop`, which hopefully never appear in the wild!
simp_lc allow dite_else_false Array.getD_eq_getD_getElem?
simp_lc allow dite_else_true Array.getD_eq_getD_getElem?

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

@[simp] theorem foldl_nat_add {f : α → Nat} {n : Nat} {l : Array α} (w : stop = l.size) :
    l.foldl (fun x y => x + f y) n 0 stop = n + (l.map f).sum := by
  subst w
  cases l
  simp

@[simp] theorem foldr_nat_add {f : α → Nat} {n : Nat} {l : Array α} (w : start = l.size) :
    l.foldr (fun x y => y + f x) n start 0 = n + (l.map f).sum := by
  subst w
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

-- FIXME:
-- simp_lc inspect Array.pmap_eq_map Array.pmap_attachWith
-- simp_lc inspect Array.pmap_eq_attachWith Array.pmap_attachWith
-- simp_lc inspect Array.pmap_attach Array.pmap_eq_map
-- simp_lc inspect Array.pmap_attach Array.pmap_eq_attachWith

-- FIXME:
-- ```
-- al : a ∈ l
-- pa : p a = true
-- ⊢ l.size - 1 = (l.eraseP p).size
-- ```
-- simp_lc inspect Array.size_eraseP_of_mem Array.length_toList
-- simp_lc inspect Array.size_toArray List.length_eraseP_of_mem
-- simp_lc inspect Array.size_toArray Array.size_eraseIdx


attribute [simp] Array.getElem_append_left Array.getElem_append_right

namespace Array

@[simp] theorem flatten_map_flatten_map {xss : Array (Array α)} {f : α → Array β} :
    (Array.map (fun xs => (Array.map f xs).flatten) xss).flatten =
      (xss.map (fun xs => xs.map f)).flatten.flatten := by
  rcases xss with ⟨xss⟩
  induction xss with
  | nil => simp
  | cons head tail ih => simp_all [Function.comp_def]

@[simp] theorem nat_sum_append {xs ys : Array Nat} : (xs ++ ys).sum = xs.sum + ys.sum := by
  rcases xs with ⟨xs⟩
  rcases ys with ⟨ys⟩
  simp

@[simp] theorem nat_sum_map_nat_sum_map {xss : Array (Array α)} {f : α → Nat} :
    (xss.map (fun y => (y.map f).sum)).sum = (xss.map (fun y => y.map f)).flatten.sum := by
  rcases xss with ⟨xss⟩
  induction xss with
  | nil => simp
  | cons head tail ih => simp_all [Function.comp_def]

@[simp] theorem nat_sum_reverse {xs : Array Nat} : xs.reverse.sum = xs.sum := by
  rcases xs with ⟨xs⟩
  simp

@[simp] theorem nat_sum_push {xs : Array Nat} {a : Nat} : (xs.push a).sum = xs.sum + a := by
  rcases xs with ⟨xs⟩
  simp

@[simp] theorem push_mkArray_self {n : Nat} {a : α} : (mkArray n a).push a = mkArray (n + 1) a := by
  rw [mkArray_succ]

attribute [simp] Array.flatten_push

@[simp] theorem pop_extract {as : Array α} {i j : Nat} :
    (as.extract i j).pop = as.extract i ((min j as.size) - 1) := by
  ext k h₁ h₂
  · simp; omega
  · simp only [size_extract, size_pop] at h₁ h₂
    simp only [getElem_extract, getElem_pop]

end Array

-- These would require using `List/Array.map_const'` as a simp lemma, and then some arithmetic.
simp_lc allow List.sum_map_nat_const_mul List.sum_map_mul_nat_const
simp_lc allow Array.foldl_nat_add Array.foldl_add_const
simp_lc allow List.foldr_nat_add List.foldr_add_const
simp_lc allow Array.sum_map_mul_nat_const Array.sum_map_nat_const_mul
simp_lc allow List.foldl_nat_add List.foldl_add_const
simp_lc allow Array.foldr_nat_add Array.foldr_add_const

-- These have the hypothesis `xs.size = xs.size - 1`,
-- from which we should deduce `xs.size = 0` and then `xs = #[]`.
-- Hopefully `grind` can do this.
simp_lc allow Array.extract_eq_pop Array.drop_eq_extract
simp_lc allow Array.extract_eq_pop Array.extract_size
simp_lc allow Array.extract_eq_pop Array.take_size

-- Should we just simp away `List.dropLast`?
simp_lc allow Array.extract_eq_pop List.extract_toArray
simp_lc allow Array.extract_eq_pop List.take_toArray

-- FIXME:
set_option maxHeartbeats 1000000 in
simp_lc allow Array.foldl_flip_append_eq_append Array.foldl_flatten'
set_option maxHeartbeats 1000000 in
simp_lc allow Array.foldr_flip_append_eq_append Array.foldr_flatten'
set_option maxHeartbeats 1000000 in
simp_lc allow Array.foldr_attachWith Array.foldr_flip_append_eq_append

simp_lc allow Array.filterMap_eq_map' Array.filterMap_map
simp_lc allow Array.foldl_append_eq_append List.foldl_toArray'
simp_lc allow Array.foldl_append_eq_append Array.foldl_attachWith
simp_lc allow Array.foldl_flip_append_eq_append List.foldl_toArray'
simp_lc allow Array.foldl_flip_append_eq_append Array.foldl_attachWith
simp_lc allow Array.foldl_cons_eq_append Array.foldl_flatten'
simp_lc allow List.foldr_toArray' Array.foldr_append_eq_append
simp_lc allow List.foldr_toArray' Array.foldr_flip_append_eq_append
simp_lc allow Array.foldr_append_eq_append Array.foldr_attachWith
simp_lc allow Array.foldr_cons_eq_append Array.foldr_flatten'
simp_lc allow Array.foldr_cons_eq_append' Array.foldr_flatten'
simp_lc allow Array.foldr_attachWith Array.foldr_cons_eq_append'
simp_lc allow List.getLast!_eq_getLast?_getD Array.getLast!_toList
simp_lc allow Array.map_const Array.map_attachWith
simp_lc allow Array.flatten_toArray Array.flatten_toArray_map
simp_lc allow Array.flatten_toArray Array.flatten_toArray_map_toArray
simp_lc allow Array.foldr_toList List.foldr_push_eq_append
simp_lc allow Array.foldr_toList List.foldr_append_eq_append
simp_lc allow Array.foldr_toList List.foldr_flip_append_eq_append
simp_lc allow Array.flatMap_singleton' Array.flatMap_subtype
simp_lc allow Array.pmap_eq_map Array.pmap_attachWith
simp_lc allow Array.pmap_eq_attachWith Array.pmap_attachWith
simp_lc allow Array.pmap_attach Array.pmap_eq_map
simp_lc allow Array.pmap_attach Array.pmap_eq_attachWith
simp_lc allow Array.extract_of_size_lt Array.extract_append
simp_lc allow Array.extract_eq_pop Array.extract_extract
simp_lc allow Array.extract_eq_pop Array.extract_append
simp_lc allow Array.extract_eq_pop Array.take_range
simp_lc allow Array.extract_size Array.extract_append
simp_lc allow Array.take_size Array.extract_extract
simp_lc allow Array.take_size Array.extract_append
simp_lc allow Array.extract_extract Array.extract_of_size_lt
simp_lc allow Array.extract_extract Array.extract_size
simp_lc allow List.take_toArray Array.extract_of_size_lt
simp_lc allow Array.extract_append_right Array.extract_of_size_lt
simp_lc allow Array.extract_append_right Array.extract_append
simp_lc allow Array.take_range Array.extract_of_size_lt
simp_lc allow Array.size_eraseP_of_mem Array.length_toList

simp_lc allow Array.foldl_toList List.foldl_append_eq_append
simp_lc allow List.foldl_push_eq_append Array.foldl_toList
simp_lc allow List.foldl_flip_append_eq_append Array.foldl_toList

/-
The actual checks happen in `tests/lean/000_simplc.lean`.
This commented out command remains here for convenience while debugging.
-/
set_option maxHeartbeats 0 in
#guard_msgs (drop info) in
simp_lc check in Array List BEq Id _root_
