module

import Std.Data

/-! Check union/intersection emptiness distributivity across the map and set APIs, including the
`Raw` variants. -/

open Std

open scoped DHashMap in
example [BEq α] [EquivBEq α] [Hashable α] [LawfulHashable α]
    {m₁ m₂ m₃ : DHashMap α β} :
    ((m₁ ∪ m₂) ∩ m₃) ~m ∅ ↔ (m₁ ∩ m₃) ~m ∅ ∧ (m₂ ∩ m₃) ~m ∅ :=
  DHashMap.union_inter_equiv_empty

open scoped DHashMap in
example [BEq α] [EquivBEq α] [Hashable α] [LawfulHashable α]
    {m₁ m₂ m₃ : DHashMap α β} :
    (m₁ ∩ (m₂ ∪ m₃)) ~m ∅ ↔ (m₁ ∩ m₂) ~m ∅ ∧ (m₁ ∩ m₃) ~m ∅ :=
  DHashMap.inter_union_equiv_empty

example [BEq α] [EquivBEq α] [Hashable α] [LawfulHashable α]
    {m₁ m₂ m₃ : ExtDHashMap α β} :
    (m₁ ∪ m₂) ∩ m₃ = ∅ ↔ m₁ ∩ m₃ = ∅ ∧ m₂ ∩ m₃ = ∅ :=
  ExtDHashMap.union_inter_eq_empty

example [BEq α] [EquivBEq α] [Hashable α] [LawfulHashable α]
    {m₁ m₂ m₃ : ExtDHashMap α β} :
    m₁ ∩ (m₂ ∪ m₃) = ∅ ↔ m₁ ∩ m₂ = ∅ ∧ m₁ ∩ m₃ = ∅ :=
  ExtDHashMap.inter_union_eq_empty

example [BEq α] [EquivBEq α] [Hashable α] [LawfulHashable α]
    {m₁ m₂ m₃ : ExtHashMap α β} :
    (m₁ ∪ m₂) ∩ m₃ = ∅ ↔ m₁ ∩ m₃ = ∅ ∧ m₂ ∩ m₃ = ∅ :=
  ExtHashMap.union_inter_eq_empty

example [BEq α] [EquivBEq α] [Hashable α] [LawfulHashable α]
    {m₁ m₂ m₃ : ExtHashMap α β} :
    m₁ ∩ (m₂ ∪ m₃) = ∅ ↔ m₁ ∩ m₂ = ∅ ∧ m₁ ∩ m₃ = ∅ :=
  ExtHashMap.inter_union_eq_empty

open scoped HashMap in
example [BEq α] [EquivBEq α] [Hashable α] [LawfulHashable α]
    {m₁ m₂ m₃ : HashMap α β} :
    ((m₁ ∪ m₂) ∩ m₃) ~m ∅ ↔ (m₁ ∩ m₃) ~m ∅ ∧ (m₂ ∩ m₃) ~m ∅ :=
  HashMap.union_inter_equiv_empty

open scoped HashMap in
example [BEq α] [EquivBEq α] [Hashable α] [LawfulHashable α]
    {m₁ m₂ m₃ : HashMap α β} :
    (m₁ ∩ (m₂ ∪ m₃)) ~m ∅ ↔ (m₁ ∩ m₂) ~m ∅ ∧ (m₁ ∩ m₃) ~m ∅ :=
  HashMap.inter_union_equiv_empty

open scoped HashSet in
example [BEq α] [EquivBEq α] [Hashable α] [LawfulHashable α]
    {m₁ m₂ m₃ : HashSet α} :
    ((m₁ ∪ m₂) ∩ m₃) ~m ∅ ↔ (m₁ ∩ m₃) ~m ∅ ∧ (m₂ ∩ m₃) ~m ∅ :=
  HashSet.union_inter_equiv_empty

open scoped HashSet in
example [BEq α] [EquivBEq α] [Hashable α] [LawfulHashable α]
    {m₁ m₂ m₃ : HashSet α} :
    (m₁ ∩ (m₂ ∪ m₃)) ~m ∅ ↔ (m₁ ∩ m₂) ~m ∅ ∧ (m₁ ∩ m₃) ~m ∅ :=
  HashSet.inter_union_equiv_empty

example [BEq α] [EquivBEq α] [Hashable α] [LawfulHashable α]
    {m₁ m₂ m₃ : ExtHashSet α} :
    (m₁ ∪ m₂) ∩ m₃ = ∅ ↔ m₁ ∩ m₃ = ∅ ∧ m₂ ∩ m₃ = ∅ :=
  ExtHashSet.union_inter_eq_empty

example [BEq α] [EquivBEq α] [Hashable α] [LawfulHashable α]
    {m₁ m₂ m₃ : ExtHashSet α} :
    m₁ ∩ (m₂ ∪ m₃) = ∅ ↔ m₁ ∩ m₂ = ∅ ∧ m₁ ∩ m₃ = ∅ :=
  ExtHashSet.inter_union_eq_empty

open scoped DTreeMap in
example {cmp : α → α → Ordering} [TransCmp cmp] {t₁ t₂ t₃ : DTreeMap α β cmp} :
    ((t₁ ∪ t₂) ∩ t₃) ~m ∅ ↔ (t₁ ∩ t₃) ~m ∅ ∧ (t₂ ∩ t₃) ~m ∅ :=
  DTreeMap.union_inter_equiv_empty

open scoped DTreeMap in
example {cmp : α → α → Ordering} [TransCmp cmp] {t₁ t₂ t₃ : DTreeMap α β cmp} :
    (t₁ ∩ (t₂ ∪ t₃)) ~m ∅ ↔ (t₁ ∩ t₂) ~m ∅ ∧ (t₁ ∩ t₃) ~m ∅ :=
  DTreeMap.inter_union_equiv_empty

example {cmp : α → α → Ordering} [TransCmp cmp] {t₁ t₂ t₃ : ExtDTreeMap α β cmp} :
    (t₁ ∪ t₂) ∩ t₃ = ∅ ↔ t₁ ∩ t₃ = ∅ ∧ t₂ ∩ t₃ = ∅ :=
  ExtDTreeMap.union_inter_eq_empty

example {cmp : α → α → Ordering} [TransCmp cmp] {t₁ t₂ t₃ : ExtDTreeMap α β cmp} :
    t₁ ∩ (t₂ ∪ t₃) = ∅ ↔ t₁ ∩ t₂ = ∅ ∧ t₁ ∩ t₃ = ∅ :=
  ExtDTreeMap.inter_union_eq_empty

open scoped TreeMap in
example {cmp : α → α → Ordering} [TransCmp cmp] {t₁ t₂ t₃ : TreeMap α β cmp} :
    ((t₁ ∪ t₂) ∩ t₃) ~m ∅ ↔ (t₁ ∩ t₃) ~m ∅ ∧ (t₂ ∩ t₃) ~m ∅ :=
  TreeMap.union_inter_equiv_empty

open scoped TreeMap in
example {cmp : α → α → Ordering} [TransCmp cmp] {t₁ t₂ t₃ : TreeMap α β cmp} :
    (t₁ ∩ (t₂ ∪ t₃)) ~m ∅ ↔ (t₁ ∩ t₂) ~m ∅ ∧ (t₁ ∩ t₃) ~m ∅ :=
  TreeMap.inter_union_equiv_empty

example {cmp : α → α → Ordering} [TransCmp cmp] {t₁ t₂ t₃ : ExtTreeMap α β cmp} :
    (t₁ ∪ t₂) ∩ t₃ = ∅ ↔ t₁ ∩ t₃ = ∅ ∧ t₂ ∩ t₃ = ∅ :=
  ExtTreeMap.union_inter_eq_empty

example {cmp : α → α → Ordering} [TransCmp cmp] {t₁ t₂ t₃ : ExtTreeMap α β cmp} :
    t₁ ∩ (t₂ ∪ t₃) = ∅ ↔ t₁ ∩ t₂ = ∅ ∧ t₁ ∩ t₃ = ∅ :=
  ExtTreeMap.inter_union_eq_empty

open scoped TreeSet in
example {cmp : α → α → Ordering} [TransCmp cmp] {t₁ t₂ t₃ : TreeSet α cmp} :
    ((t₁ ∪ t₂) ∩ t₃) ~m ∅ ↔ (t₁ ∩ t₃) ~m ∅ ∧ (t₂ ∩ t₃) ~m ∅ :=
  TreeSet.union_inter_equiv_empty

open scoped TreeSet in
example {cmp : α → α → Ordering} [TransCmp cmp] {t₁ t₂ t₃ : TreeSet α cmp} :
    (t₁ ∩ (t₂ ∪ t₃)) ~m ∅ ↔ (t₁ ∩ t₂) ~m ∅ ∧ (t₁ ∩ t₃) ~m ∅ :=
  TreeSet.inter_union_equiv_empty

example {cmp : α → α → Ordering} [TransCmp cmp] {t₁ t₂ t₃ : ExtTreeSet α cmp} :
    (t₁ ∪ t₂) ∩ t₃ = ∅ ↔ t₁ ∩ t₃ = ∅ ∧ t₂ ∩ t₃ = ∅ :=
  ExtTreeSet.union_inter_eq_empty

example {cmp : α → α → Ordering} [TransCmp cmp] {t₁ t₂ t₃ : ExtTreeSet α cmp} :
    t₁ ∩ (t₂ ∪ t₃) = ∅ ↔ t₁ ∩ t₂ = ∅ ∧ t₁ ∩ t₃ = ∅ :=
  ExtTreeSet.inter_union_eq_empty

example [BEq α] [EquivBEq α] [Hashable α] [LawfulHashable α]
    {m₁ m₂ m₃ : DHashMap.Raw α β} (h₁ : m₁.WF) (h₂ : m₂.WF) (h₃ : m₃.WF) :
    DHashMap.Raw.Equiv ((m₁ ∪ m₂) ∩ m₃) (∅ : DHashMap.Raw α β) ↔
      DHashMap.Raw.Equiv (m₁ ∩ m₃) (∅ : DHashMap.Raw α β) ∧
        DHashMap.Raw.Equiv (m₂ ∩ m₃) (∅ : DHashMap.Raw α β) :=
  DHashMap.Raw.union_inter_equiv_empty h₁ h₂ h₃

example [BEq α] [EquivBEq α] [Hashable α] [LawfulHashable α]
    {m₁ m₂ m₃ : DHashMap.Raw α β} (h₁ : m₁.WF) (h₂ : m₂.WF) (h₃ : m₃.WF) :
    DHashMap.Raw.Equiv (m₁ ∩ (m₂ ∪ m₃)) (∅ : DHashMap.Raw α β) ↔
      DHashMap.Raw.Equiv (m₁ ∩ m₂) (∅ : DHashMap.Raw α β) ∧
        DHashMap.Raw.Equiv (m₁ ∩ m₃) (∅ : DHashMap.Raw α β) :=
  DHashMap.Raw.inter_union_equiv_empty h₁ h₂ h₃

example [BEq α] [EquivBEq α] [Hashable α] [LawfulHashable α]
    {m₁ m₂ m₃ : HashMap.Raw α β} (h₁ : m₁.WF) (h₂ : m₂.WF) (h₃ : m₃.WF) :
    HashMap.Raw.Equiv ((m₁ ∪ m₂) ∩ m₃) (∅ : HashMap.Raw α β) ↔
      HashMap.Raw.Equiv (m₁ ∩ m₃) (∅ : HashMap.Raw α β) ∧
        HashMap.Raw.Equiv (m₂ ∩ m₃) (∅ : HashMap.Raw α β) :=
  HashMap.Raw.union_inter_equiv_empty h₁ h₂ h₃

example [BEq α] [EquivBEq α] [Hashable α] [LawfulHashable α]
    {m₁ m₂ m₃ : HashSet.Raw α} (h₁ : m₁.WF) (h₂ : m₂.WF) (h₃ : m₃.WF) :
    HashSet.Raw.Equiv ((m₁ ∪ m₂) ∩ m₃) (∅ : HashSet.Raw α) ↔
      HashSet.Raw.Equiv (m₁ ∩ m₃) (∅ : HashSet.Raw α) ∧
        HashSet.Raw.Equiv (m₂ ∩ m₃) (∅ : HashSet.Raw α) :=
  HashSet.Raw.union_inter_equiv_empty h₁ h₂ h₃

example {cmp : α → α → Ordering} [TransCmp cmp]
    {t₁ t₂ t₃ : DTreeMap.Raw α β cmp} (h₁ : t₁.WF) (h₂ : t₂.WF) (h₃ : t₃.WF) :
    DTreeMap.Raw.Equiv ((t₁ ∪ t₂) ∩ t₃) (∅ : DTreeMap.Raw α β cmp) ↔
      DTreeMap.Raw.Equiv (t₁ ∩ t₃) (∅ : DTreeMap.Raw α β cmp) ∧
        DTreeMap.Raw.Equiv (t₂ ∩ t₃) (∅ : DTreeMap.Raw α β cmp) :=
  DTreeMap.Raw.union_inter_equiv_empty h₁ h₂ h₃

example {cmp : α → α → Ordering} [TransCmp cmp]
    {t₁ t₂ t₃ : TreeMap.Raw α β cmp} (h₁ : t₁.WF) (h₂ : t₂.WF) (h₃ : t₃.WF) :
    TreeMap.Raw.Equiv ((t₁ ∪ t₂) ∩ t₃) (∅ : TreeMap.Raw α β cmp) ↔
      TreeMap.Raw.Equiv (t₁ ∩ t₃) (∅ : TreeMap.Raw α β cmp) ∧
        TreeMap.Raw.Equiv (t₂ ∩ t₃) (∅ : TreeMap.Raw α β cmp) :=
  TreeMap.Raw.union_inter_equiv_empty h₁ h₂ h₃

example {cmp : α → α → Ordering} [TransCmp cmp]
    {t₁ t₂ t₃ : TreeSet.Raw α cmp} (h₁ : t₁.WF) (h₂ : t₂.WF) (h₃ : t₃.WF) :
    TreeSet.Raw.Equiv ((t₁ ∪ t₂) ∩ t₃) (∅ : TreeSet.Raw α cmp) ↔
      TreeSet.Raw.Equiv (t₁ ∩ t₃) (∅ : TreeSet.Raw α cmp) ∧
        TreeSet.Raw.Equiv (t₂ ∩ t₃) (∅ : TreeSet.Raw α cmp) :=
  TreeSet.Raw.union_inter_equiv_empty h₁ h₂ h₃
