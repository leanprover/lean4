/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Różowski
-/
module

prelude
public import Std.Data.DTreeMap.DecidableEquiv
public import Std.Data.TreeMap.Basic

public section

/-!
# Decidable equivalence for `TreeMap`
-/

open Std.DTreeMap

namespace Std.TreeMap

instance {α : Type u} {β : Type v} {cmp : α → α → Ordering} [TransCmp cmp] [LawfulEqCmp cmp] [BEq β] [LawfulBEq β] {t₁ t₂ : TreeMap α β cmp} : Decidable (t₁ ~m t₂) :=
  let : Ord α := ⟨cmp⟩;
  decidable_of_iff _ ⟨fun h => ⟨h⟩, fun h => h.1⟩

end Std.TreeMap
