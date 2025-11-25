/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

prelude
public import Lean.SimpLC.Exceptions.Root
public import Lean.SimpLC.Exceptions.Array
public import Lean.SimpLC.Exceptions.BitVec
public import Lean.SimpLC.Exceptions.Bool
public import Lean.SimpLC.Exceptions.Fin
public import Lean.SimpLC.Exceptions.List
public import Lean.SimpLC.Exceptions.Monad
public import Lean.SimpLC.Exceptions.Nat
public import Lean.SimpLC.Exceptions.Option
public import Lean.SimpLC.Exceptions.Prod
public import Lean.SimpLC.Exceptions.Std
public import Lean.SimpLC.Exceptions.Subtype
public import Lean.SimpLC.Exceptions.Sum

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
simp_lc ignore forIn'_eq_forIn


namespace Option

attribute [simp] Option.map_attach

end Option

namespace Array

@[simp] theorem foldlM_attach_toList [Monad m] {xs : Array α}
    (f : β → { x // x ∈ xs.toList } → m β) (init : β) :
    List.foldlM f init xs.toList.attach =
      Array.foldlM (fun b ⟨x, m⟩ => f b ⟨x, by simpa using m⟩) init xs.attach := by
  cases xs
  simp only [toList_toArray]
  rw [List.attach_toArray]
  simp only [List.attachWith_mem_toArray, size_toArray, List.length_map, List.length_attach,
    List.foldlM_toArray', List.foldlM_map]

@[simp] theorem foldrM_attach_toList [Monad m] [LawfulMonad m]{xs : Array α}
    (f : { x // x ∈ xs.toList } → β → m β) (init : β) :
    List.foldrM f init xs.toList.attach =
      Array.foldrM (fun ⟨x, m⟩ b => f ⟨x, by simpa using m⟩ b) init xs.attach := by
  cases xs
  simp only [toList_toArray]
  rw [List.attach_toArray]
  simp [List.foldrM_map]

@[simp] theorem foldl_attach_toList {xs : Array α} (f : β → { x // x ∈ xs.toList } → β) (init : β) :
    List.foldl f init xs.toList.attach =
      Array.foldl (fun b ⟨x, m⟩ => f b ⟨x, by simpa using m⟩) init xs.attach := by
  cases xs
  simp [List.foldl_map]

@[simp] theorem foldr_attach_toList {xs : Array α} (f : { x // x ∈ xs.toList } → β → β) (init : β) :
    List.foldr f init xs.toList.attach =
      Array.foldr (fun ⟨x, m⟩ b => f ⟨x, by simpa using m⟩ b) init xs.attach := by
  cases xs
  simp [List.foldr_map]

end Array

/-
Check *everything*.
-/
-- set_option maxHeartbeats 0 in
-- #time
-- #guard_msgs (drop info) in
-- simp_lc check
