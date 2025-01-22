/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Orderedtree.DTreeMap.Lemmas
import Orderedtree.TreeMap.Basic

/-!
# API lemmas for `TreeMap`
-/

set_option linter.missingDocs true
set_option autoImplicit false

open Std.DTreeMap.Internal

universe u v

namespace Std.TreeMap

variable {α : Type u} {β : Type v} {cmp : α → α → Ordering} {t : TreeMap α β cmp}

theorem isEmpty_empty : (empty : TreeMap α β cmp).isEmpty :=
  DTreeMap.isEmpty_empty

theorem mem_iff_contains {k : α} : k ∈ t ↔ t.contains k :=
  DTreeMap.mem_iff_contains

theorem contains_congr [TransCmp cmp] {k k' : α} (hab : cmp k k' == .eq) :
    t.contains k = t.contains k' :=
  DTreeMap.contains_congr hab

theorem mem_congr [TransCmp cmp] {k k' : α} (hab : cmp k k' == .eq) : k ∈ t ↔ k' ∈ t :=
  DTreeMap.mem_congr hab

theorem contains_empty {k : α} : (empty : TreeMap α β cmp).contains k = false :=
  DTreeMap.contains_empty

theorem mem_empty {k : α} : k ∉ (empty : TreeMap α β cmp) :=
  DTreeMap.mem_empty

theorem contains_insert [h : TransCmp cmp] {k a : α} {v : β} :
    (t.insert k v).contains a = (cmp k a == .eq || t.contains a) :=
  DTreeMap.contains_insert

end Std.TreeMap
