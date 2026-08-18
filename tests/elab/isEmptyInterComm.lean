import Std.Data.ExtHashMap

open Std
open scoped DHashMap

/-! Check intersection emptiness symmetry for extensional and non-extensional hash maps. -/

example [BEq α] [EquivBEq α] [Hashable α] [LawfulHashable α]
    {m₁ m₂ : DHashMap α β} :
    (m₁ ∩ m₂) ~m ∅ ↔ (m₂ ∩ m₁) ~m ∅ :=
  DHashMap.inter_equiv_empty_comm

example [BEq α] [EquivBEq α] [Hashable α] [LawfulHashable α]
    {m₁ m₂ : ExtHashMap α β} :
    m₁ ∩ m₂ = ∅ ↔ m₂ ∩ m₁ = ∅ :=
  ExtHashMap.inter_eq_empty_comm
