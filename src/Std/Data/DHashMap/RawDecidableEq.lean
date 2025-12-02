/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Różowski
-/
module

prelude
public import Std.Data.DHashMap.Internal.RawLemmas
import all Std.Data.DHashMap.Raw

public section

/-!
# Decidable equivalence for `DHashMap.Raw`
-/

open Std.DHashMap.Internal

namespace Std.DHashMap

instance {α : Type u} {β : α → Type v} [DecidableEq α] [Hashable α] [∀ k, DecidableEq (β k)] {m₁ m₂ : Raw α β} (h₁ : m₁.WF) (h₂ : m₂.WF) : Decidable (m₁.Equiv m₂) :=
  @Raw₀.Equiv.decide _ _ _ _ _ ⟨m₁, h₁.size_buckets_pos⟩ ⟨m₂, h₂.size_buckets_pos⟩ h₁ h₂

end Std.DHashMap
