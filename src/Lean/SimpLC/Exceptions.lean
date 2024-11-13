/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
prelude
import Lean.SimpLC.Exceptions.Root
import Lean.SimpLC.Exceptions.Array
import Lean.SimpLC.Exceptions.BitVec
import Lean.SimpLC.Exceptions.Bool
import Lean.SimpLC.Exceptions.Fin
import Lean.SimpLC.Exceptions.List
import Lean.SimpLC.Exceptions.Monad
import Lean.SimpLC.Exceptions.Nat
import Lean.SimpLC.Exceptions.Option
import Lean.SimpLC.Exceptions.Prod
import Lean.SimpLC.Exceptions.Std
import Lean.SimpLC.Exceptions.Subtype
import Lean.SimpLC.Exceptions.Sum

/-
The actual checks happen in `tests/lean/000_simplc.lean`.
These commented out commands remain here for convenience while debugging.
-/

/-
Ideally downstream libraries would preserve the fact that the
`simp_lc check in <...builtin types ...>` command below succeeds
(possibly by adding further `simp_lc allow` and `simp_lc ignore` commands).
Even better, they would add `_root_` to the check as well,
if they do not intentionally occupy the root namespace.
-/
-- #guard_msgs (drop info) in
-- simp_lc check in String Char Float USize UInt64 UInt32 UInt16 UInt8 PLift ULift Prod Sum Range
--   Subtype ByteArray FloatArray List Option Array Int Nat Bool Id
--   Monad LawfulFunctor LawfulApplicative LawfulMonad LawfulSingleton Std



simp_lc ignore forIn'_eq_forIn

-- These would be resolved by a `ring` tactic, but are beyond `simp +arith`.
simp_lc allow List.foldl_cons List.foldl_add_const
simp_lc allow List.foldr_cons List.foldr_add_const
simp_lc allow List.foldr_append List.foldr_add_const
simp_lc allow List.foldl_append List.foldl_add_const


simp_lc inspect Std.DHashMap.Raw.contains_keys Std.DHashMap.Internal.Raw₀.contains_keys
simp_lc inspect Std.DHashMap.Internal.Raw₀.mem_keys Std.DHashMap.Raw.mem_keys

simp_lc inspect List.elem_eq_mem Std.DHashMap.Internal.Raw₀.contains_keys
simp_lc inspect List.elem_eq_mem Std.HashMap.Raw.contains_keys
simp_lc inspect Std.HashSet.contains_toList List.elem_eq_mem
simp_lc inspect Std.HashSet.Raw.contains_toList List.elem_eq_mem
simp_lc inspect Std.DHashMap.contains_keys List.elem_eq_mem
simp_lc inspect Std.HashMap.contains_keys List.elem_eq_mem
simp_lc inspect Std.DHashMap.Raw.contains_keys List.elem_eq_mem

simp_lc ignore forIn'_eq_forIn

namespace Option

-- Neither of these fire?!

@[simp] theorem attach_toList (o : Option α) :
    o.toList.attach = o.attach.toList.map fun ⟨a, h⟩ => ⟨a, by simpa using h⟩ := by
  cases o <;> simp

@[simp] theorem attach_toList' (o : Option α) :
    o.toList.attach = (o.attach.map fun ⟨a, h⟩ => ⟨a, by simpa using h⟩).toList := by
  cases o <;> simp

end Option

-- Nope, not a good idea, but why?
-- attribute [simp] List.foldlM_map List.foldrM_map

simp_lc inspect List.forIn'_yield_eq_foldlM Option.forIn'_toList
simp_lc inspect List.forIn'_yield_eq_foldlM List.forIn'_cons
simp_lc inspect List.forIn'_yield_eq_foldlM Array.forIn'_toList
simp_lc inspect Option.forIn'_toList List.forIn'_yield_eq_foldl
simp_lc inspect List.forIn'_cons List.forIn'_yield_eq_foldl
simp_lc inspect Array.forIn'_toList List.forIn'_yield_eq_foldl
simp_lc inspect List.forIn_yield_eq_foldlM Option.forIn_toList
simp_lc inspect List.forIn_yield_eq_foldlM Array.forIn_toList
simp_lc inspect List.forIn_yield_eq_foldl Option.forIn_toList
simp_lc inspect List.forIn_yield_eq_foldl Array.forIn_toList

simp_lc inspect List.findSome?_guard Array.findSome?_toList

/-
Check *everything*.
-/
-- set_option maxHeartbeats 0 in
-- #time
-- #guard_msgs (drop info) in
-- simp_lc check
