/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Różowski
-/
module

prelude
public import Std.Data.HashMap.RawDecidableEquiv
public import Std.Data.HashSet.Raw

public section

/-!
# Decidable equivalence for `HashSet.Raw`
-/

open Std.HashMap.Raw

namespace Std.HashSet.Raw

instance instDecidableEquiv {α : Type u} [BEq α] [LawfulBEq α] [Hashable α] {m₁ m₂ : Raw α} (h₁ : m₁.WF) (h₂ : m₂.WF) : Decidable (m₁ ~m m₂) :=
  let : Decidable (m₁.1 ~m m₂.1) := HashMap.Raw.instDecidableEquiv h₁.out h₂.out;
  decidable_of_iff _ ⟨fun h => ⟨h⟩, fun h => h.1⟩

end Std.HashSet.Raw
