/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Paul Reichert
-/
prelude
import Std.Data.DTreeMap.Internal.Lemmas
import Std.Data.DTreeMap.Basic

/-!
# Dependent tree map lemmas

This file contains lemmas about `Std.Data.DTreeMap`. Most of the lemmas require
`TransCmp cmp` for the comparison function `cmp`.
-/

open Std.DTreeMap.Internal

set_option linter.missingDocs true
set_option autoImplicit false

universe u v

namespace Std.DTreeMap

variable {α : Type u} {β : α → Type v} {cmp : α → α → Ordering} {t : DTreeMap α β cmp}

@[simp]
theorem isEmpty_emptyc : (∅ : DTreeMap α β cmp).isEmpty :=
  Impl.isEmpty_empty

@[simp]
theorem isEmpty_insert [TransCmp cmp] {k : α} {v : β k} :
    (t.insert k v).isEmpty = false :=
  Impl.isEmpty_insert t.wf

theorem mem_iff_contains {k : α} : k ∈ t ↔ t.contains k :=
  Impl.mem_iff_contains

theorem contains_congr [TransCmp cmp] {k k' : α} (hab : cmp k k' = .eq) :
    t.contains k = t.contains k' :=
  Impl.contains_congr t.wf hab

theorem mem_congr [TransCmp cmp] {k k' : α} (hab : cmp k k' = .eq) : k ∈ t ↔ k' ∈ t :=
  Impl.mem_congr t.wf hab

@[simp]
theorem isEmpty_insertIfNew [TransCmp cmp] {k : α} {v : β k} :
    (t.insertIfNew k v).isEmpty = false :=
  Impl.isEmpty_insertIfNew t.wf

end Std.DTreeMap
