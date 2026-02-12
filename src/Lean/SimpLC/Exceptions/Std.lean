/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

prelude
import Std
import Lean.SimpLC.Exceptions.Root

set_option Elab.async false -- `simplc` crashes on the command line with a 139 without this.

-- Internal implementation details of `DHashMap`.
simp_lc ignore Std.DHashMap.Internal.Raw₀.contains_keys
simp_lc ignore Std.DHashMap.Internal.Raw₀.mem_keys

-- I don't understand this next set: `simp` seems to close the goal.
example {α : Type _} [BEq α] [EquivBEq α] (a : α) : (a == a) = true := by simp
example {α : Type _} {β : Type _} [BEq α] [Hashable α] {m : Std.HashMap α β}
    [LawfulHashable α] {a : α} {_ : β} [EquivBEq α] [LawfulHashable α] :
    (a == a) = true ∨ a ∈ m :=
  by simp

simp_lc allow Std.HashSet.Raw.contains_insert Std.HashSet.Raw.contains_insert_self
simp_lc allow Std.DHashMap.Raw.mem_insert Std.DHashMap.Raw.mem_insert_self
simp_lc allow Std.HashMap.Raw.mem_insert_self Std.HashMap.Raw.mem_insert
simp_lc allow Std.HashSet.Raw.mem_insert Std.HashSet.Raw.mem_insert_self
simp_lc allow Std.DHashMap.Raw.contains_insert Std.DHashMap.Raw.contains_insert_self
simp_lc allow Std.HashMap.Raw.contains_insert Std.HashMap.Raw.contains_insert_self

-- TODO: I'm confused by these ones,
-- which I can't seem to construct simp lemmas to resolve.
simp_lc allow Std.HashSet.insert_eq_insert LawfulSingleton.insert_empty_eq
simp_lc allow Std.HashMap.insert_eq_insert LawfulSingleton.insert_empty_eq
simp_lc allow Std.DHashMap.insert_eq_insert LawfulSingleton.insert_empty_eq
simp_lc allow Std.HashSet.Raw.insert_eq_insert LawfulSingleton.insert_empty_eq
simp_lc allow Std.HashMap.Raw.insert_eq_insert LawfulSingleton.insert_empty_eq
simp_lc allow LawfulSingleton.insert_empty_eq Std.DHashMap.Raw.insert_eq_insert

simp_lc allow Std.DHashMap.Raw.contains_keys Std.DHashMap.Internal.Raw₀.contains_keys
simp_lc allow Std.HashMap.Raw.get!_eq_getElem! Std.HashMap.Raw.getElem!_modify_self
simp_lc allow Std.HashMap.Raw.get?_eq_getElem? Std.HashMap.Raw.getElem?_modify_self
simp_lc allow Std.DHashMap.Internal.Raw₀.mem_keys Std.DHashMap.Raw.mem_keys
simp_lc allow Std.HashMap.Raw.get_eq_getElem Std.HashMap.Raw.getElem_modify_self

/-
The actual checks happen in `tests/lean/000_simplc.lean`.
This commented out command remains here for convenience while debugging.
-/
-- set_option maxHeartbeats 1000000 in
-- #guard_msgs (drop info) in
-- simp_lc check in Std Id LawfulSingleton _root_
