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

namespace Std.HashSet.Raw

instance {α : Type u} [DecidableEq α] [Hashable α] {m₁ m₂ : Raw α} (h₁ : m₁.WF) (h₂ : m₂.WF) : Decidable (m₁.Equiv m₂) :=
  let : Decidable (m₁.1.Equiv m₂.1) := HashMap.Raw.instDecidableEquivOfDecidableEqOfWF h₁.out h₂.out; decidable_of_iff _ ⟨fun h => ⟨h⟩, fun h => h.1⟩

end Std.HashSet.Raw
