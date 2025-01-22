/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Orderedtree.DTreeMap.Internal.Lemmas
import Orderedtree.DTreeMap.Basic

/-!
# API lemmas for `DTreeMap`
-/

set_option linter.missingDocs true
set_option autoImplicit false

open Std.DTreeMap.Internal

universe u v

namespace Std.DTreeMap

attribute [local instance] TransOrd.ofTransCmp

variable {α : Type u} {β : α → Type v} {cmp : α → α → Ordering} {t : DTreeMap α β cmp}

theorem isEmpty_empty : (empty : DTreeMap α β cmp).isEmpty :=
  Impl.isEmpty_empty

theorem mem_iff_contains {k : α} : k ∈ t ↔ t.contains k :=
  Impl.mem_iff_contains

theorem contains_congr [TransCmp cmp] {k k' : α} (hab : cmp k k' == .eq) :
    t.contains k = t.contains k' :=
  Impl.contains_congr t.wf hab

theorem mem_congr [TransCmp cmp] {k k' : α} (hab : cmp k k' == .eq) : k ∈ t ↔ k' ∈ t :=
  Impl.mem_congr t.wf hab

theorem contains_empty {k : α} : (empty : DTreeMap α β cmp).contains k = false :=
  Impl.contains_empty

theorem mem_empty {k : α} : k ∉ (empty : DTreeMap α β cmp) :=
  Impl.mem_empty

theorem contains_insert [TransCmp cmp] {k k' : α} {v : β k} :
    (t.insert k v).contains k' = (cmp k k' == .eq || t.contains k') :=
  Impl.contains_insert t.wf

end Std.DTreeMap
