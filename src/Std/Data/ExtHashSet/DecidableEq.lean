/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Różowski
-/
module

prelude
public import Std.Data.ExtDHashMap.Basic
public import Std.Data.ExtHashSet.Basic
public import Std.Data.ExtHashSet.Lemmas
public import Std.Data.DHashMap.DecidableEq

public section

/-!
# Decidable equality for `ExtHashSet`
-/

namespace Std.ExtHashSet

open scoped Std.ExtDHashMap

instance {α : Type u} [DecidableEq α] [Hashable α] : DecidableEq (ExtHashSet α) :=
  fun ⟨⟨m₁⟩⟩ ⟨⟨m₂⟩⟩ => @decidable_of_decidable_of_iff (ExtDHashMap.Const.beq_unit m₁ m₂) _ _
    (by rw [mk.injEq, ExtHashMap.mk.injEq]; exact ⟨by apply ExtDHashMap.Const.eq_of_beq_unit_eq_true, by apply ExtDHashMap.Const.beq_unit_of_eq⟩)

end Std.ExtHashSet
