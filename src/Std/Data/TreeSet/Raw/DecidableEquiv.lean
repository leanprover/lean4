/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Różowski
-/
module

prelude

public import Std.Data.TreeMap.Raw.DecidableEquiv
public import Std.Data.TreeSet.Raw.Basic

public section

/-!
# Decidable equivalence for `TreeSet.Raw`
-/

open Std.TreeMap.Raw

namespace Std.TreeSet.Raw

instance {α : Type u} {cmp : α → α → Ordering} [TransCmp cmp] [LawfulEqCmp cmp] [DecidableEq α] {t₁ t₂ : Raw α cmp} (h₁ : t₁.WF) (h₂ : t₂.WF) : Decidable (t₁ ~m t₂) :=
  let : Ord α := ⟨cmp⟩;
  let : Decidable (t₁.inner ~m t₂.inner) := Std.TreeMap.Raw.instDecidableEquivOfTransCmpOfLawfulEqCmpOfDecidableEqOfWF h₁ h₂;
  decidable_of_iff (t₁.inner ~m t₂.inner) ⟨fun h => ⟨h⟩, fun h => h.1⟩

end Std.TreeSet.Raw
