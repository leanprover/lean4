module

prelude
public import Std.Data.ExtDHashMap.Basic
public import Std.Data.ExtDHashMap.Lemmas
public import Std.Data.DHashMap.DecidableEq

public section
namespace Std.ExtDHashMap

open scoped Std.DHashMap

variable {α : Type u} {β : α → Type v} [DecidableEq α] [Hashable α] [∀ k, DecidableEq (β k)] (m₁ m₂ : ExtDHashMap α β)

def decidableEq : Decidable (m₁ = m₂) := by
  have decBEq : Decidable (beq m₁ m₂ = true) := inferInstance
  apply @decidable_of_decidable_of_iff (beq m₁ m₂ = true) (m₁ = m₂) decBEq
  constructor
  case mp =>
    induction m₁
    case mk a =>
      induction m₂
      case mk b =>
        intro hyp
        apply sound
        apply DHashMap.Equiv_of_beq_eq_true
        simp [BEq.beq]
        sorry
  case mpr =>
    sorry



end Std.ExtDHashMap
