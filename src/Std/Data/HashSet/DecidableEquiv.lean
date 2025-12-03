/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Różowski
-/
module

prelude
public import Std.Data.HashMap.DecidableEquiv
public import Std.Data.HashSet.Basic

public section

/-!
# Decidable equivalence for `HashSet`
-/

namespace Std.HashSet

instance {α : Type u} [DecidableEq α] [Hashable α] (m₁ m₂ : HashSet α) : Decidable (m₁ ~m m₂) :=
  @decidable_of_iff _ _ ⟨fun h => ⟨h⟩, fun h => h.1⟩ <| HashMap.instDecidableEquivOfDecidableEq m₁.inner m₂.inner

end Std.HashSet
