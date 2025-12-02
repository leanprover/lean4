/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Różowski
-/
module

prelude
public import Std.Data.ExtDHashMap.Basic
public import Std.Data.ExtHashMap.Basic
public import Std.Data.ExtHashMap.Lemmas
public import Std.Data.DHashMap.DecidableEq

public section

/-!
# Decidable equality for `ExtHashMap`
-/

namespace Std.ExtHashMap

open scoped Std.DHashMap

instance {α : Type u} {β : Type v} [DecidableEq α] [Hashable α] [DecidableEq β] : DecidableEq (ExtHashMap α β) :=
  fun ⟨m₁⟩ ⟨m₂⟩ => @decidable_of_decidable_of_iff (ExtDHashMap.Const.beq m₁ m₂) _ _
    (by rw [mk.injEq]; exact ⟨by apply ExtDHashMap.Const.eq_of_beq_eq_true, by apply ExtDHashMap.Const.beq_of_eq⟩)

end Std.ExtHashMap
