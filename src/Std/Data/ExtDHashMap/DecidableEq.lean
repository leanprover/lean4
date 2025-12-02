/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Różowski
-/
module

prelude
public import Std.Data.ExtDHashMap.Basic
public import Std.Data.ExtDHashMap.Lemmas
public import Std.Data.DHashMap.DecidableEq

public section

/-!
# Decidable equality for `ExtDHashMap`
-/

namespace Std.ExtDHashMap

open scoped Std.DHashMap

instance {α : Type u} {β : α → Type v} [DecidableEq α] [Hashable α] [∀ k, DecidableEq (β k)] : DecidableEq (ExtDHashMap α β) :=
  fun m₁ m₂ => @decidable_of_decidable_of_iff (m₁ == m₂) _ _ ⟨by simp, by simp⟩

end Std.ExtDHashMap
