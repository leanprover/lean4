/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Różowski
-/
module

prelude
public import Std.Data.HashMap.RawLemmas
import all Std.Data.HashMap.Raw

public section

/-!
# Decidable equivalence for `DHashMap.Raw`
-/

open Std.DHashMap.Internal

namespace Std.HashMap

instance {α : Type u} {β : Type v} [DecidableEq α] [Hashable α] [DecidableEq β] {m₁ m₂ : Raw α β} (h₁ : m₁.WF) (h₂ : m₂.WF) : Decidable (m₁.Equiv m₂) := by
  apply @decidable_of_iff (m₁.Equiv m₂) (m₁.inner.Equiv m₂.inner) (by exact ⟨fun h => ⟨h⟩, fun h => h.1⟩) <| @Raw₀.Equiv.decide α (fun _ => β) _ _ _ ⟨m₁.inner, h₁.out.size_buckets_pos⟩ ⟨m₂.inner, h₂.out.size_buckets_pos⟩ h₁.out h₂.out

end Std.HashMap
