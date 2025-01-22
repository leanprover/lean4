/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Orderedtree.TreeMap.Lemmas
import Orderedtree.TreeSet.Basic

/-!
# API lemmas for `TreeMap`
-/

set_option linter.missingDocs true
set_option autoImplicit false

open Std.DTreeMap.Internal

universe u v

namespace Std.TreeSet

variable {α : Type u} {cmp : α → α → Ordering} {t : TreeSet α cmp}

theorem isEmpty_empty : (empty : TreeSet α cmp).isEmpty :=
  TreeMap.isEmpty_empty

theorem mem_iff_contains {k : α} : k ∈ t ↔ t.contains k :=
  TreeMap.mem_iff_contains

theorem contains_congr [TransCmp cmp] {k k' : α} (hab : cmp k k' == .eq) :
    t.contains k = t.contains k' :=
  TreeMap.contains_congr hab

theorem mem_congr [TransCmp cmp] {k k' : α} (hab : cmp k k' == .eq) : k ∈ t ↔ k' ∈ t :=
  TreeMap.mem_congr hab

theorem contains_empty {k : α} : (empty : TreeSet α cmp).contains k = false :=
  TreeMap.contains_empty

theorem mem_empty {k : α} : k ∉ (empty : TreeSet α cmp) :=
  TreeMap.mem_empty

theorem contains_insert [h : TransCmp cmp] (t : TreeSet α cmp) {k a : α} :
    (t.insert k).contains a = (cmp k a == .eq || t.contains a) :=
  TreeMap.contains_insert

end Std.TreeSet
