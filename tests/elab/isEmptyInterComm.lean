module

import Std.Data

/-! Check intersection emptiness symmetry across map and set APIs, including Raw variants. -/

open Std

open scoped DHashMap in
example [BEq α] [EquivBEq α] [Hashable α] [LawfulHashable α]
    {m₁ m₂ : DHashMap α β} :
    (m₁ ∩ m₂) ~m ∅ ↔ (m₂ ∩ m₁) ~m ∅ :=
  DHashMap.inter_equiv_empty_comm

example [BEq α] [EquivBEq α] [Hashable α] [LawfulHashable α]
    {m₁ m₂ : ExtHashMap α β} :
    m₁ ∩ m₂ = ∅ ↔ m₂ ∩ m₁ = ∅ :=
  ExtHashMap.inter_eq_empty_comm

open scoped HashMap in
example [BEq α] [EquivBEq α] [Hashable α] [LawfulHashable α]
    {m₁ m₂ : HashMap α β} :
    (m₁ ∩ m₂) ~m ∅ ↔ (m₂ ∩ m₁) ~m ∅ :=
  HashMap.inter_equiv_empty_comm

open scoped HashSet in
example [BEq α] [EquivBEq α] [Hashable α] [LawfulHashable α]
    {m₁ m₂ : HashSet α} :
    (m₁ ∩ m₂) ~m ∅ ↔ (m₂ ∩ m₁) ~m ∅ :=
  HashSet.inter_equiv_empty_comm

example [BEq α] [EquivBEq α] [Hashable α] [LawfulHashable α]
    {m₁ m₂ : ExtHashSet α} :
    m₁ ∩ m₂ = ∅ ↔ m₂ ∩ m₁ = ∅ :=
  ExtHashSet.inter_eq_empty_comm

open scoped DTreeMap in
example {cmp : α → α → Ordering} [TransCmp cmp] {t₁ t₂ : DTreeMap α β cmp} :
    (t₁ ∩ t₂) ~m ∅ ↔ (t₂ ∩ t₁) ~m ∅ :=
  DTreeMap.inter_equiv_empty_comm

example {cmp : α → α → Ordering} [TransCmp cmp] {t₁ t₂ : ExtDTreeMap α β cmp} :
    t₁ ∩ t₂ = ∅ ↔ t₂ ∩ t₁ = ∅ :=
  ExtDTreeMap.inter_eq_empty_comm

open scoped TreeMap in
example {cmp : α → α → Ordering} [TransCmp cmp] {t₁ t₂ : TreeMap α β cmp} :
    (t₁ ∩ t₂) ~m ∅ ↔ (t₂ ∩ t₁) ~m ∅ :=
  TreeMap.inter_equiv_empty_comm

example {cmp : α → α → Ordering} [TransCmp cmp] {t₁ t₂ : ExtTreeMap α β cmp} :
    t₁ ∩ t₂ = ∅ ↔ t₂ ∩ t₁ = ∅ :=
  ExtTreeMap.inter_eq_empty_comm

open scoped TreeSet in
example {cmp : α → α → Ordering} [TransCmp cmp] {t₁ t₂ : TreeSet α cmp} :
    (t₁ ∩ t₂) ~m ∅ ↔ (t₂ ∩ t₁) ~m ∅ :=
  TreeSet.inter_equiv_empty_comm

example {cmp : α → α → Ordering} [TransCmp cmp] {t₁ t₂ : ExtTreeSet α cmp} :
    t₁ ∩ t₂ = ∅ ↔ t₂ ∩ t₁ = ∅ :=
  ExtTreeSet.inter_eq_empty_comm

example [BEq α] [EquivBEq α] [Hashable α] [LawfulHashable α]
    {m₁ m₂ : DHashMap.Raw α β} (h₁ : m₁.WF) (h₂ : m₂.WF) :
    DHashMap.Raw.Equiv (DHashMap.Raw.inter m₁ m₂) (∅ : DHashMap.Raw α β) ↔
      DHashMap.Raw.Equiv (DHashMap.Raw.inter m₂ m₁) (∅ : DHashMap.Raw α β) :=
  DHashMap.Raw.inter_equiv_empty_comm h₁ h₂

example [BEq α] [EquivBEq α] [Hashable α] [LawfulHashable α]
    {m₁ m₂ : HashMap.Raw α β} (h₁ : m₁.WF) (h₂ : m₂.WF) :
    HashMap.Raw.Equiv (HashMap.Raw.inter m₁ m₂) (∅ : HashMap.Raw α β) ↔
      HashMap.Raw.Equiv (HashMap.Raw.inter m₂ m₁) (∅ : HashMap.Raw α β) :=
  HashMap.Raw.inter_equiv_empty_comm h₁ h₂

example [BEq α] [EquivBEq α] [Hashable α] [LawfulHashable α]
    {m₁ m₂ : HashSet.Raw α} (h₁ : m₁.WF) (h₂ : m₂.WF) :
    HashSet.Raw.Equiv (HashSet.Raw.inter m₁ m₂) (∅ : HashSet.Raw α) ↔
      HashSet.Raw.Equiv (HashSet.Raw.inter m₂ m₁) (∅ : HashSet.Raw α) :=
  HashSet.Raw.inter_equiv_empty_comm h₁ h₂

example {cmp : α → α → Ordering} [TransCmp cmp]
    {t₁ t₂ : DTreeMap.Raw α β cmp} (h₁ : t₁.WF) (h₂ : t₂.WF) :
    DTreeMap.Raw.Equiv (DTreeMap.Raw.inter t₁ t₂) (∅ : DTreeMap.Raw α β cmp) ↔
      DTreeMap.Raw.Equiv (DTreeMap.Raw.inter t₂ t₁) (∅ : DTreeMap.Raw α β cmp) :=
  DTreeMap.Raw.inter_equiv_empty_comm h₁ h₂

example {cmp : α → α → Ordering} [TransCmp cmp]
    {t₁ t₂ : TreeMap.Raw α β cmp} (h₁ : t₁.WF) (h₂ : t₂.WF) :
    TreeMap.Raw.Equiv (TreeMap.Raw.inter t₁ t₂) (∅ : TreeMap.Raw α β cmp) ↔
      TreeMap.Raw.Equiv (TreeMap.Raw.inter t₂ t₁) (∅ : TreeMap.Raw α β cmp) :=
  TreeMap.Raw.inter_equiv_empty_comm h₁ h₂

example {cmp : α → α → Ordering} [TransCmp cmp]
    {t₁ t₂ : TreeSet.Raw α cmp} (h₁ : t₁.WF) (h₂ : t₂.WF) :
    TreeSet.Raw.Equiv (TreeSet.Raw.inter t₁ t₂) (∅ : TreeSet.Raw α cmp) ↔
      TreeSet.Raw.Equiv (TreeSet.Raw.inter t₂ t₁) (∅ : TreeSet.Raw α cmp) :=
  TreeSet.Raw.inter_equiv_empty_comm h₁ h₂
