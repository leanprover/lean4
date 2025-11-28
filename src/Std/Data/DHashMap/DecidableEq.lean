/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Różowski
-/
module

prelude
public import Std.Data.DHashMap.Internal.RawLemmas
import all Std.Data.DHashMap.Basic
public import Std.Data.DHashMap.AdditionalOperations
import all Std.Data.DHashMap.AdditionalOperations

public section

/-!
# Decidable equality for DHashMaps
-/

open Std.DHashMap.Internal


namespace Std.DHashMap

variable {α : Type u} {β : α → Type v} [DecidableEq α] [Hashable α] [∀ k, DecidableEq (β k)] (m₁ m₂ : DHashMap α β)

def Equiv.decide : Decidable (m₁ ~m m₂) :=
  @decidable_of_iff _ _ ⟨fun h => ⟨h⟩, fun h => h.1⟩ <|
    @Raw₀.Equiv.decide _ _ _ _ _ ⟨m₁.1, m₁.2.size_buckets_pos⟩ ⟨m₂.1, m₂.2.size_buckets_pos⟩ m₁.2 m₂.2

instance : Decidable (m₁ ~m m₂) := Equiv.decide m₁ m₂


end Std.DHashMap
