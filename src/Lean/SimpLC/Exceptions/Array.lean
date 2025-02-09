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
simp_lc ignore Array.foldl_subtype
simp_lc ignore Array.foldr_subtype
simp_lc ignore Array.foldlM_subtype
simp_lc ignore Array.foldrM_subtype
simp_lc ignore Array.mapFinIdx_eq_mapIdx
simp_lc ignore Array.findSome?_subtype
simp_lc ignore Array.findFinIdx?_subtype
simp_lc ignore Array.findIdx_subtype
simp_lc ignore Array.findIdx?_subtype

simp_lc inspect Array.contains_eq_mem Array.contains_push
simp_lc inspect Array.filterMap_reverse Array.filterMap_eq_filter
simp_lc inspect Array.filterMap_map Array.filterMap_eq_map
simp_lc inspect Array.filterMap_eq_filter Array.filterMap_flatten
simp_lc inspect Array.filterMap_eq_filter Array.filterMap_push_some
simp_lc inspect Array.filterMap_eq_filter Array.filterMap_mkArray_of_isSome
simp_lc inspect Array.filterMap_eq_filter Array.filterMap_map
simp_lc inspect Array.filterMap_eq_filter Array.filterMap_append
simp_lc inspect Array.filterMap_eq_filter Array.filterMap_attachWith
simp_lc inspect Array.filterMap_some Array.filterMap_attachWith
simp_lc inspect Array.filterMap_attachWith Array.filterMap_eq_map
simp_lc inspect Array.foldl_flatten' Array.foldl_add_const
simp_lc inspect Array.foldl_append' Array.foldl_add_const
simp_lc inspect Array.foldl_push_eq_append Array.foldl_flatten'
simp_lc inspect Array.foldl_push_eq_append Array.foldl_attachWith
simp_lc inspect Array.foldl_subtype' Array.foldl_flatten'
simp_lc inspect Array.foldl_subtype' Array.foldl_push_eq_append
simp_lc inspect Array.foldl_subtype' Array.foldl_add_const
simp_lc inspect Array.findSomeRev?_eq_findSome?_reverse Array.findSomeRev?_push_of_isSome
simp_lc inspect Array.findSomeRev?_eq_findSome?_reverse Array.findSomeRev?_push_of_isNone
simp_lc inspect Array.foldr_push' Array.foldr_flip_push_eq_append
simp_lc inspect Array.foldr_push' Array.foldr_add_const
simp_lc inspect Array.foldr_append' Array.foldr_add_const
simp_lc inspect Array.foldr_flip_push_eq_append Array.foldr_flatten'
simp_lc inspect Array.foldr_flip_push_eq_append Array.foldr_subtype'
simp_lc inspect Array.foldr_add_const Array.foldr_flatten'
simp_lc inspect Array.foldr_add_const Array.foldr_subtype'
simp_lc inspect Array.foldr_subtype' Array.foldr_flatten'
simp_lc inspect Array.foldr_attachWith Array.foldr_flip_push_eq_append
simp_lc inspect Array.forIn'_map Array.forIn'_yield_eq_foldlM
simp_lc inspect Array.forIn'_map Array.forIn'_yield_eq_foldl
simp_lc inspect List.forIn'_toArray Array.forIn'_yield_eq_foldlM
simp_lc inspect List.forIn'_toArray Array.forIn'_yield_eq_foldl
simp_lc inspect List.forIn'_yield_eq_foldlM Array.forIn'_toList
simp_lc inspect Array.forIn'_toList List.forIn'_yield_eq_foldl
simp_lc inspect Array.getElem?_eq_getElem Array.getElem?_pmap
simp_lc inspect Array.getElem?_eq_getElem Array.getElem?_map
simp_lc inspect Array.getElem?_eq_getElem Array.getElem?_mapFinIdx
simp_lc inspect Array.getElem?_eq_getElem Array.getElem?_attachWith
simp_lc inspect Array.getElem?_eq_getElem Array.getElem?_attach
simp_lc inspect Array.getElem?_mapIdx Array.getElem?_eq_getElem
simp_lc inspect Array.getElem?_unattach Array.getElem?_eq_getElem
simp_lc inspect List.lex_toArray Array.lex_empty
simp_lc inspect Array.forIn_map Array.forIn_yield_eq_foldlM
simp_lc inspect Array.forIn_map Array.forIn_yield_eq_foldl
simp_lc inspect Array.map_flatten Array.map_const
simp_lc inspect Array.map_push Array.map_const
simp_lc inspect Array.map_pop Array.map_const
simp_lc inspect Array.findSome?_mkArray_of_pos Array.findSome?_mkArray_of_isSome
simp_lc inspect List.count_toArray Array.count_singleton
simp_lc inspect Array.foldr_toList List.foldr_push'
simp_lc inspect List.foldr_push Array.foldr_toList
simp_lc inspect List.foldr_cons_eq_append' Array.foldr_toList
simp_lc inspect List.foldr_cons_eq_append Array.foldr_toList
simp_lc inspect Array.flatMap_toArray Array.flatMap_id'
simp_lc inspect Array.flatMap_toArray Array.flatMap_id
simp_lc inspect Array.flatMap_id' List.flatMap_toArray
simp_lc inspect Array.flatMap_id List.flatMap_toArray
simp_lc inspect Array.pmap_eq_map Array.pmap_attachWith
simp_lc inspect Array.pmap_eq_attachWith Array.pmap_attachWith
simp_lc inspect Array.pmap_attach Array.pmap_eq_map
simp_lc inspect Array.pmap_attach Array.pmap_eq_attachWith
simp_lc inspect Array.append_assoc Array.append_push
simp_lc inspect Array.append_assoc Array.append_singleton
simp_lc inspect Array.size_eraseP_of_mem Array.length_toList
simp_lc inspect Array.size_toArray List.length_eraseP_of_mem
simp_lc inspect Array.size_toArray Array.size_eraseIdx
simp_lc inspect List.foldl_push' Array.foldl_toList
simp_lc inspect List.foldl_flip_cons_eq_append Array.foldl_toList
simp_lc inspect List.foldl_flip_cons_eq_append' Array.foldl_toList
simp_lc inspect Array.set_getElem_self Array.set_append_right
simp_lc inspect Array.set_append_left Array.set_getElem_self

/-
The actual checks happen in `tests/lean/000_simplc.lean`.
This commented out command remains here for convenience while debugging.
-/
#guard_msgs (drop info) in
simp_lc check in Array List BEq Id _root_
