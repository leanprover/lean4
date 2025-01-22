/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Orderedtree.TreeMap.RawLemmas
import Orderedtree.TreeSet.Raw

/-!
# API lemmas for `TreeMap.Raw`
-/

set_option linter.missingDocs true
set_option autoImplicit false

universe u v

namespace Std.TreeSet.Raw

attribute [local instance] TransOrd.ofTransCmp

variable {α : Type u} {β : Type v} {cmp : α → α → Ordering} {t : TreeSet.Raw α cmp}

theorem isEmpty_empty : (empty : TreeSet.Raw α cmp).isEmpty :=
  TreeMap.Raw.isEmpty_empty

theorem mem_iff_contains {k : α} : k ∈ t ↔ t.contains k :=
  TreeMap.Raw.mem_iff_contains

theorem contains_congr [TransCmp cmp] (h : t.WF) {k k' : α} (hab : cmp k k' == .eq) :
    t.contains k = t.contains k' :=
  TreeMap.Raw.contains_congr h hab

theorem mem_congr [TransCmp cmp] (h : t.WF) {k k' : α} (hab : cmp k k' == .eq) : k ∈ t ↔ k' ∈ t :=
  TreeMap.Raw.mem_congr h hab

theorem contains_empty {k : α} : (empty : TreeSet.Raw α cmp).contains k = false :=
  TreeMap.Raw.contains_empty

theorem mem_empty {k : α} : k ∉ (empty : TreeSet.Raw α cmp) :=
  TreeMap.Raw.mem_empty

theorem contains_insert [h : TransCmp cmp] (h : t.WF) {k a : α} :
    (t.insert k).contains a = (cmp k a == .eq || t.contains a) :=
  TreeMap.Raw.contains_insert h

end Std.TreeSet.Raw
