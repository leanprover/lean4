/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Różowski
-/
module

prelude
public import Std.Data.ExtDHashMap.Basic
public import Std.Data.ExtDHashMap.Lemmas
public import Std.Data.DHashMap.DecidableEq

public section
namespace Std.ExtDHashMap

open scoped Std.DHashMap

variable {α : Type u} {β : α → Type v} [DecidableEq α] [Hashable α] [∀ k, DecidableEq (β k)] (m₁ m₂ : ExtDHashMap α β)

def decidableEq : Decidable (m₁ = m₂) := @decidable_of_decidable_of_iff _ _ _ ⟨by apply ExtDHashMap.eq_of_beq_true, by apply ExtDHashMap.beq_of_eq⟩

instance : DecidableEq (ExtDHashMap α β) := decidableEq

end Std.ExtDHashMap
