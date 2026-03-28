/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Różowski
-/
module

prelude
public import Std.Data.DHashMap.RawDecidableEquiv
public import Std.Data.HashMap.Raw

public section

/-!
# Decidable equivalence for `HashMap.Raw`
-/

open Std.DHashMap.Raw

namespace Std.HashMap.Raw

instance instDecidableEquiv {α : Type u} {β : Type v} [BEq α] [LawfulBEq α] [Hashable α] [BEq β] [LawfulBEq β] {m₁ m₂ : Raw α β} (h₁ : m₁.WF) (h₂ : m₂.WF) : Decidable (m₁ ~m m₂) :=
  let : Decidable (m₁.1 ~m m₂.1) := DHashMap.Raw.instDecidableEquiv h₁.out h₂.out;
  decidable_of_iff _ ⟨fun h => ⟨h⟩, fun h => h.1⟩

end Std.HashMap.Raw
