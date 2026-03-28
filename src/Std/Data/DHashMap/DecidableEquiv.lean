/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Różowski
-/
module

prelude
public import Std.Data.DHashMap.Internal.RawLemmas

public section

/-!
# Decidable equivalence for `DHashMap`
-/

open Std.DHashMap.Internal

namespace Std.DHashMap

instance {α : Type u} {β : α → Type v} [BEq α] [LawfulBEq α] [Hashable α] [∀ k, BEq (β k)] [∀ k, LawfulBEq (β k)] (m₁ m₂ : DHashMap α β) : Decidable (m₁ ~m m₂) :=
  let : Decidable (m₁.1.Equiv m₂.1) := Raw₀.decidableEquiv ⟨m₁.1, m₁.2.size_buckets_pos⟩ ⟨m₂.1, m₂.2.size_buckets_pos⟩ m₁.2 m₂.2;
  decidable_of_iff _ ⟨fun h => ⟨h⟩, fun h => h.1⟩

end Std.DHashMap
