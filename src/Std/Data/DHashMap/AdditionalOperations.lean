/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
prelude
import Std.Data.DHashMap.Internal.Raw
import Std.Data.DHashMap.Internal.WF

/-!
# Additional dependent hash map operations

This file defines the operations `map` and `filterMap` on `Std.Data.DHashMap`.
We currently do not provide lemmas for these functions.
-/

open Std.DHashMap.Internal

set_option linter.missingDocs true
set_option autoImplicit false

universe u u' v v' w

variable {α : Type u} {α' : Type u'} {β : α → Type v} {β' : α' → Type v'} {δ : α → Type w}

namespace Std.DHashMap

namespace Raw

open Internal.Raw

theorem WF.filterMap [BEq α] [Hashable α] {m : Raw α β} (h : m.WF)
    {f : (a : α) → β a → Option (δ a)} : (m.filterMap f).WF := by
  simpa only [filterMap_eq h] using
    .wf (Raw₀.filterMap f ⟨m, h.size_buckets_pos⟩).2 (Raw₀.wfImp_filterMap (WF.out h))

theorem WF.map [BEq α] [Hashable α] {m : Raw α β} (h : m.WF) {f : (a : α) → β a → δ a} :
    (m.map f).WF := by
  simpa only [map_eq h] using .wf (Raw₀.map f ⟨m, h.size_buckets_pos⟩).2 (Raw₀.wfImp_map (WF.out h))

/-- Internal implementation detail of the hash map -/
@[inline] def pmapEntries {P : (a : α) → (b : β a) → Prop }
    (f : (a : α) → (b : β a) → P a b → ((a' : α') × β' a'))
    (m : Raw α β) (H : ∀ a b, ⟨a, b⟩ ∈ m.toList → P a b) : Raw α' β' :=
  if h : 0 < m.buckets.size then
    Raw₀.pmapEntries f ⟨m, h⟩ (by rwa [←Std.DHashMap.Internal.Raw.toList_eq_toListModel])
  else ∅ -- will never happen for well-formed inputs

-- TODO: Can't put it in `/Internal/Raw` because we need `toList_eq_toListModel`
theorem pmapEntries_eq [BEq α] [Hashable α] {m : Raw α β} (h : m.WF) {P : (a : α) → (b : β a) → Prop}
    (f : (a : α) → (b : β a) → P a b → ((a' : α') × β' a'))
    {H : ∀ a b, ⟨a, b⟩ ∈ m.toList → P a b} :
    m.pmapEntries f H = Raw₀.pmapEntries f ⟨m, h.size_buckets_pos⟩
      (by rwa [←toList_eq_toListModel]) := by
  simp [Raw.pmapEntries, h.size_buckets_pos]

-- NOTE: we need the Lawful/EquivBEq instances on `α` because the `.wf` only gives us that it holds
-- for `α'`
theorem WF.pmapEntries [BEq α] [EquivBEq α] [BEq α'] [Hashable α] [LawfulHashable α] [Hashable α']
    {m : Raw α β} {P : (a : α) → β a → Prop}
    (f : (a : α) → (b : β a) → P a b → ((a' : α') × β' a'))
    (h₁ : ∀ a b h, hash (f a b h).1 = hash a)
    (h₂ : ∀ a₁ b₁ a₂ b₂ h₁ h₂, (f a₁ b₁ h₁).1 == (f a₂ b₂ h₂).1 → a₁ == a₂)
    {H : ∀ a b, ⟨a, b⟩ ∈ m.toList → P a b} (h : m.WF) : (m.pmapEntries f H).WF := by
  simpa only [pmapEntries_eq h] using
    .wf (Raw₀.pmapEntries f ⟨m, h.size_buckets_pos⟩ sorry).2 (Raw₀.wfImp_pmapEntries h₁ h₂ (WF.out h))

end Raw

@[inline, inherit_doc Raw.filterMap] def filterMap [BEq α] [Hashable α]
    (f : (a : α) → β a → Option (δ a)) (m : DHashMap α β) : DHashMap α δ :=
  ⟨Raw₀.filterMap f ⟨m.1, m.2.size_buckets_pos⟩,
   .wf (Raw₀.filterMap f ⟨m.1, m.2.size_buckets_pos⟩).2 (Raw₀.wfImp_filterMap (Raw.WF.out m.2))⟩

@[inline, inherit_doc Raw.map] def map [BEq α] [Hashable α] (f : (a : α) → β a → δ a)
    (m : DHashMap α β) : DHashMap α δ :=
  ⟨Raw₀.map f ⟨m.1, m.2.size_buckets_pos⟩,
   .wf (Raw₀.map f ⟨m.1, m.2.size_buckets_pos⟩).2 (Raw₀.wfImp_map (Raw.WF.out m.2))⟩

end Std.DHashMap
