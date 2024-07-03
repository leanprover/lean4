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

universe u v w

variable {α : Type u} {β : α → Type v} {γ : Type w} {δ : α → Type w}

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
