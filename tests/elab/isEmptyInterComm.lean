import Std.Data

open Std

/-! Check intersection emptiness symmetry across the public map and set APIs. -/

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
