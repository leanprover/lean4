module

import Std.Data

/-! Check union/intersection emptiness distributivity across the hash map APIs. -/

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
