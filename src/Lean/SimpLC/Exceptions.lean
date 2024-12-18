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
simp_lc ignore forIn'_eq_forIn


namespace Option

attribute [simp] Option.map_attach

@[simp] theorem elim_pmap {p : α → Prop} (f : (a : α) → p a → β) (o : Option α) (H : ∀ (a : α), a ∈ o → p a) (g : γ) (g' : β → γ) :
    (o.pmap f H).elim g g' =
       o.pelim g (fun a h => g' (f a (H a h))) := by
  cases o <;> simp

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

-- These would become confluent with `List.foldlM_map` as a simp lemma,
-- but that causes other problems (which we should document).
simp_lc allow List.forIn'_yield_eq_foldlM List.forIn'_cons
simp_lc allow List.forIn'_cons List.forIn'_yield_eq_foldl

/-
Check *everything*.
-/
-- set_option maxHeartbeats 0 in
-- #time
-- #guard_msgs (drop info) in
-- simp_lc check
