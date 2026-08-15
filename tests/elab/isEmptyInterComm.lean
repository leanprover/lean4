import Std.Data.ExtHashMap

open Std

/-! Check that intersection emptiness symmetry implies symmetry of disjoint hash maps. -/

example [BEq α] [EquivBEq α] [Hashable α] [LawfulHashable α]
    {m₁ m₂ : ExtHashMap α β} (h : m₁ ∩ m₂ = ∅) :
    m₂ ∩ m₁ = ∅ := by
  rw [← ExtHashMap.isEmpty_iff] at h ⊢
  rw [ExtHashMap.isEmpty_inter_comm]
  exact h
