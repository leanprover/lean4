/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Orderedtree.DTreeMap.RawLemmas
import Orderedtree.TreeMap.Raw

/-!
# API lemmas for `TreeMap.Raw`
-/

set_option linter.missingDocs true
set_option autoImplicit false

universe u v

namespace Std.TreeMap.Raw

variable {α : Type u} {β : Type v} {cmp : α → α → Ordering} {t : TreeMap.Raw α β cmp}

attribute [local instance] TransOrd.ofTransCmp

theorem isEmpty_empty : (empty : TreeMap.Raw α β cmp).isEmpty :=
  DTreeMap.Raw.isEmpty_empty

theorem mem_iff_contains {k : α} : k ∈ t ↔ t.contains k :=
  DTreeMap.Raw.mem_iff_contains

theorem contains_congr [TransCmp cmp] (h : t.WF) {k k' : α} (hab : cmp k k' == .eq) :
    t.contains k = t.contains k' :=
  DTreeMap.Raw.contains_congr h hab

theorem mem_congr [TransCmp cmp] (h : t.WF) {k k' : α} (hab : cmp k k' == .eq) : k ∈ t ↔ k' ∈ t :=
  DTreeMap.Raw.mem_congr h hab

theorem contains_empty {k : α} : (empty : TreeMap.Raw α β cmp).contains k = false :=
  DTreeMap.Raw.contains_empty

theorem mem_empty {k : α} : k ∉ (empty : TreeMap.Raw α β cmp) :=
  DTreeMap.Raw.mem_empty

theorem contains_insert [h : TransCmp cmp] (h : t.WF) {k a : α} {v : β} :
    (t.insert k v).contains a = (cmp k a == .eq || t.contains a) :=
  DTreeMap.Raw.contains_insert h

end Std.TreeMap.Raw
