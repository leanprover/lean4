module

import Std.Data

/-! Check union/intersection emptiness distributivity across the map and set APIs, including the
`Raw` variants. -/

open Std

example [BEq α] [EquivBEq α] [Hashable α] [LawfulHashable α] {m₁ m₂ m₃ : DHashMap α β} :
    ((m₁ ∪ m₂) ∩ m₃).isEmpty = ((m₁ ∩ m₃).isEmpty && (m₂ ∩ m₃).isEmpty) :=
  DHashMap.isEmpty_union_inter

example [BEq α] [EquivBEq α] [Hashable α] [LawfulHashable α] {m₁ m₂ m₃ : DHashMap α β} :
    (m₁ ∩ (m₂ ∪ m₃)).isEmpty = ((m₁ ∩ m₂).isEmpty && (m₁ ∩ m₃).isEmpty) :=
  DHashMap.isEmpty_inter_union

example [BEq α] [EquivBEq α] [Hashable α] [LawfulHashable α] {m₁ m₂ m₃ : ExtDHashMap α β} :
    ((m₁ ∪ m₂) ∩ m₃).isEmpty = ((m₁ ∩ m₃).isEmpty && (m₂ ∩ m₃).isEmpty) :=
  ExtDHashMap.isEmpty_union_inter

example [BEq α] [EquivBEq α] [Hashable α] [LawfulHashable α] {m₁ m₂ m₃ : ExtDHashMap α β} :
    (m₁ ∩ (m₂ ∪ m₃)).isEmpty = ((m₁ ∩ m₂).isEmpty && (m₁ ∩ m₃).isEmpty) :=
  ExtDHashMap.isEmpty_inter_union

example [BEq α] [EquivBEq α] [Hashable α] [LawfulHashable α] {m₁ m₂ m₃ : HashMap α β} :
    ((m₁ ∪ m₂) ∩ m₃).isEmpty = ((m₁ ∩ m₃).isEmpty && (m₂ ∩ m₃).isEmpty) :=
  HashMap.isEmpty_union_inter

example [BEq α] [EquivBEq α] [Hashable α] [LawfulHashable α] {m₁ m₂ m₃ : HashMap α β} :
    (m₁ ∩ (m₂ ∪ m₃)).isEmpty = ((m₁ ∩ m₂).isEmpty && (m₁ ∩ m₃).isEmpty) :=
  HashMap.isEmpty_inter_union

example [BEq α] [EquivBEq α] [Hashable α] [LawfulHashable α] {m₁ m₂ m₃ : ExtHashMap α β} :
    ((m₁ ∪ m₂) ∩ m₃).isEmpty = ((m₁ ∩ m₃).isEmpty && (m₂ ∩ m₃).isEmpty) :=
  ExtHashMap.isEmpty_union_inter

example [BEq α] [EquivBEq α] [Hashable α] [LawfulHashable α] {m₁ m₂ m₃ : ExtHashMap α β} :
    (m₁ ∩ (m₂ ∪ m₃)).isEmpty = ((m₁ ∩ m₂).isEmpty && (m₁ ∩ m₃).isEmpty) :=
  ExtHashMap.isEmpty_inter_union

example [BEq α] [EquivBEq α] [Hashable α] [LawfulHashable α] {m₁ m₂ m₃ : HashSet α} :
    ((m₁ ∪ m₂) ∩ m₃).isEmpty = ((m₁ ∩ m₃).isEmpty && (m₂ ∩ m₃).isEmpty) :=
  HashSet.isEmpty_union_inter

example [BEq α] [EquivBEq α] [Hashable α] [LawfulHashable α] {m₁ m₂ m₃ : HashSet α} :
    (m₁ ∩ (m₂ ∪ m₃)).isEmpty = ((m₁ ∩ m₂).isEmpty && (m₁ ∩ m₃).isEmpty) :=
  HashSet.isEmpty_inter_union

example [BEq α] [EquivBEq α] [Hashable α] [LawfulHashable α] {m₁ m₂ m₃ : ExtHashSet α} :
    ((m₁ ∪ m₂) ∩ m₃).isEmpty = ((m₁ ∩ m₃).isEmpty && (m₂ ∩ m₃).isEmpty) :=
  ExtHashSet.isEmpty_union_inter

example [BEq α] [EquivBEq α] [Hashable α] [LawfulHashable α] {m₁ m₂ m₃ : ExtHashSet α} :
    (m₁ ∩ (m₂ ∪ m₃)).isEmpty = ((m₁ ∩ m₂).isEmpty && (m₁ ∩ m₃).isEmpty) :=
  ExtHashSet.isEmpty_inter_union

example {cmp : α → α → Ordering} [TransCmp cmp] {t₁ t₂ t₃ : DTreeMap α β cmp} :
    ((t₁ ∪ t₂) ∩ t₃).isEmpty = ((t₁ ∩ t₃).isEmpty && (t₂ ∩ t₃).isEmpty) :=
  DTreeMap.isEmpty_union_inter

example {cmp : α → α → Ordering} [TransCmp cmp] {t₁ t₂ t₃ : DTreeMap α β cmp} :
    (t₁ ∩ (t₂ ∪ t₃)).isEmpty = ((t₁ ∩ t₂).isEmpty && (t₁ ∩ t₃).isEmpty) :=
  DTreeMap.isEmpty_inter_union

example {cmp : α → α → Ordering} [TransCmp cmp] {t₁ t₂ t₃ : ExtDTreeMap α β cmp} :
    ((t₁ ∪ t₂) ∩ t₃).isEmpty = ((t₁ ∩ t₃).isEmpty && (t₂ ∩ t₃).isEmpty) :=
  ExtDTreeMap.isEmpty_union_inter

example {cmp : α → α → Ordering} [TransCmp cmp] {t₁ t₂ t₃ : ExtDTreeMap α β cmp} :
    (t₁ ∩ (t₂ ∪ t₃)).isEmpty = ((t₁ ∩ t₂).isEmpty && (t₁ ∩ t₃).isEmpty) :=
  ExtDTreeMap.isEmpty_inter_union

example {cmp : α → α → Ordering} [TransCmp cmp] {t₁ t₂ t₃ : TreeMap α β cmp} :
    ((t₁ ∪ t₂) ∩ t₃).isEmpty = ((t₁ ∩ t₃).isEmpty && (t₂ ∩ t₃).isEmpty) :=
  TreeMap.isEmpty_union_inter

example {cmp : α → α → Ordering} [TransCmp cmp] {t₁ t₂ t₃ : TreeMap α β cmp} :
    (t₁ ∩ (t₂ ∪ t₃)).isEmpty = ((t₁ ∩ t₂).isEmpty && (t₁ ∩ t₃).isEmpty) :=
  TreeMap.isEmpty_inter_union

example {cmp : α → α → Ordering} [TransCmp cmp] {t₁ t₂ t₃ : ExtTreeMap α β cmp} :
    ((t₁ ∪ t₂) ∩ t₃).isEmpty = ((t₁ ∩ t₃).isEmpty && (t₂ ∩ t₃).isEmpty) :=
  ExtTreeMap.isEmpty_union_inter

example {cmp : α → α → Ordering} [TransCmp cmp] {t₁ t₂ t₃ : ExtTreeMap α β cmp} :
    (t₁ ∩ (t₂ ∪ t₃)).isEmpty = ((t₁ ∩ t₂).isEmpty && (t₁ ∩ t₃).isEmpty) :=
  ExtTreeMap.isEmpty_inter_union

example {cmp : α → α → Ordering} [TransCmp cmp] {t₁ t₂ t₃ : TreeSet α cmp} :
    ((t₁ ∪ t₂) ∩ t₃).isEmpty = ((t₁ ∩ t₃).isEmpty && (t₂ ∩ t₃).isEmpty) :=
  TreeSet.isEmpty_union_inter

example {cmp : α → α → Ordering} [TransCmp cmp] {t₁ t₂ t₃ : TreeSet α cmp} :
    (t₁ ∩ (t₂ ∪ t₃)).isEmpty = ((t₁ ∩ t₂).isEmpty && (t₁ ∩ t₃).isEmpty) :=
  TreeSet.isEmpty_inter_union

example {cmp : α → α → Ordering} [TransCmp cmp] {t₁ t₂ t₃ : ExtTreeSet α cmp} :
    ((t₁ ∪ t₂) ∩ t₃).isEmpty = ((t₁ ∩ t₃).isEmpty && (t₂ ∩ t₃).isEmpty) :=
  ExtTreeSet.isEmpty_union_inter

example {cmp : α → α → Ordering} [TransCmp cmp] {t₁ t₂ t₃ : ExtTreeSet α cmp} :
    (t₁ ∩ (t₂ ∪ t₃)).isEmpty = ((t₁ ∩ t₂).isEmpty && (t₁ ∩ t₃).isEmpty) :=
  ExtTreeSet.isEmpty_inter_union

example [BEq α] [EquivBEq α] [Hashable α] [LawfulHashable α]
    {m₁ m₂ m₃ : DHashMap.Raw α β} (h₁ : m₁.WF) (h₂ : m₂.WF) (h₃ : m₃.WF) :
    ((m₁ ∪ m₂) ∩ m₃).isEmpty = ((m₁ ∩ m₃).isEmpty && (m₂ ∩ m₃).isEmpty) :=
  DHashMap.Raw.isEmpty_union_inter h₁ h₂ h₃

example [BEq α] [EquivBEq α] [Hashable α] [LawfulHashable α]
    {m₁ m₂ m₃ : DHashMap.Raw α β} (h₁ : m₁.WF) (h₂ : m₂.WF) (h₃ : m₃.WF) :
    (m₁ ∩ (m₂ ∪ m₃)).isEmpty = ((m₁ ∩ m₂).isEmpty && (m₁ ∩ m₃).isEmpty) :=
  DHashMap.Raw.isEmpty_inter_union h₁ h₂ h₃

example [BEq α] [EquivBEq α] [Hashable α] [LawfulHashable α]
    {m₁ m₂ m₃ : HashMap.Raw α β} (h₁ : m₁.WF) (h₂ : m₂.WF) (h₃ : m₃.WF) :
    ((m₁ ∪ m₂) ∩ m₃).isEmpty = ((m₁ ∩ m₃).isEmpty && (m₂ ∩ m₃).isEmpty) :=
  HashMap.Raw.isEmpty_union_inter h₁ h₂ h₃

example [BEq α] [EquivBEq α] [Hashable α] [LawfulHashable α]
    {m₁ m₂ m₃ : HashMap.Raw α β} (h₁ : m₁.WF) (h₂ : m₂.WF) (h₃ : m₃.WF) :
    (m₁ ∩ (m₂ ∪ m₃)).isEmpty = ((m₁ ∩ m₂).isEmpty && (m₁ ∩ m₃).isEmpty) :=
  HashMap.Raw.isEmpty_inter_union h₁ h₂ h₃

example [BEq α] [EquivBEq α] [Hashable α] [LawfulHashable α]
    {m₁ m₂ m₃ : HashSet.Raw α} (h₁ : m₁.WF) (h₂ : m₂.WF) (h₃ : m₃.WF) :
    ((m₁ ∪ m₂) ∩ m₃).isEmpty = ((m₁ ∩ m₃).isEmpty && (m₂ ∩ m₃).isEmpty) :=
  HashSet.Raw.isEmpty_union_inter h₁ h₂ h₃

example [BEq α] [EquivBEq α] [Hashable α] [LawfulHashable α]
    {m₁ m₂ m₃ : HashSet.Raw α} (h₁ : m₁.WF) (h₂ : m₂.WF) (h₃ : m₃.WF) :
    (m₁ ∩ (m₂ ∪ m₃)).isEmpty = ((m₁ ∩ m₂).isEmpty && (m₁ ∩ m₃).isEmpty) :=
  HashSet.Raw.isEmpty_inter_union h₁ h₂ h₃

example {cmp : α → α → Ordering} [TransCmp cmp]
    {t₁ t₂ t₃ : DTreeMap.Raw α β cmp} (h₁ : t₁.WF) (h₂ : t₂.WF) (h₃ : t₃.WF) :
    ((t₁ ∪ t₂) ∩ t₃).isEmpty = ((t₁ ∩ t₃).isEmpty && (t₂ ∩ t₃).isEmpty) :=
  DTreeMap.Raw.isEmpty_union_inter h₁ h₂ h₃

example {cmp : α → α → Ordering} [TransCmp cmp]
    {t₁ t₂ t₃ : DTreeMap.Raw α β cmp} (h₁ : t₁.WF) (h₂ : t₂.WF) (h₃ : t₃.WF) :
    (t₁ ∩ (t₂ ∪ t₃)).isEmpty = ((t₁ ∩ t₂).isEmpty && (t₁ ∩ t₃).isEmpty) :=
  DTreeMap.Raw.isEmpty_inter_union h₁ h₂ h₃

example {cmp : α → α → Ordering} [TransCmp cmp]
    {t₁ t₂ t₃ : TreeMap.Raw α β cmp} (h₁ : t₁.WF) (h₂ : t₂.WF) (h₃ : t₃.WF) :
    ((t₁ ∪ t₂) ∩ t₃).isEmpty = ((t₁ ∩ t₃).isEmpty && (t₂ ∩ t₃).isEmpty) :=
  TreeMap.Raw.isEmpty_union_inter h₁ h₂ h₃

example {cmp : α → α → Ordering} [TransCmp cmp]
    {t₁ t₂ t₃ : TreeMap.Raw α β cmp} (h₁ : t₁.WF) (h₂ : t₂.WF) (h₃ : t₃.WF) :
    (t₁ ∩ (t₂ ∪ t₃)).isEmpty = ((t₁ ∩ t₂).isEmpty && (t₁ ∩ t₃).isEmpty) :=
  TreeMap.Raw.isEmpty_inter_union h₁ h₂ h₃

example {cmp : α → α → Ordering} [TransCmp cmp]
    {t₁ t₂ t₃ : TreeSet.Raw α cmp} (h₁ : t₁.WF) (h₂ : t₂.WF) (h₃ : t₃.WF) :
    ((t₁ ∪ t₂) ∩ t₃).isEmpty = ((t₁ ∩ t₃).isEmpty && (t₂ ∩ t₃).isEmpty) :=
  TreeSet.Raw.isEmpty_union_inter h₁ h₂ h₃

example {cmp : α → α → Ordering} [TransCmp cmp]
    {t₁ t₂ t₃ : TreeSet.Raw α cmp} (h₁ : t₁.WF) (h₂ : t₂.WF) (h₃ : t₃.WF) :
    (t₁ ∩ (t₂ ∪ t₃)).isEmpty = ((t₁ ∩ t₂).isEmpty && (t₁ ∩ t₃).isEmpty) :=
  TreeSet.Raw.isEmpty_inter_union h₁ h₂ h₃

example {cmp : α → α → Ordering} [TransCmp cmp] {t₁ t₂ t₃ t₄ : TreeSet α cmp} :
    ((t₁ ∪ t₂) ∩ (t₃ ∪ t₄)).isEmpty =
      ((t₁ ∩ t₃).isEmpty && (t₂ ∩ t₃).isEmpty && ((t₁ ∩ t₄).isEmpty && (t₂ ∩ t₄).isEmpty)) := by
  simp
