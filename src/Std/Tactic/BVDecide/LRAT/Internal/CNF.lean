/-
Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Clune
-/
prelude
import Std.Tactic.BVDecide.LRAT.Internal.Formula.Class

set_option grind.warning false

namespace Std.Tactic.BVDecide
namespace LRAT
namespace Internal

open Clause Formula Std Sat

namespace Literal

theorem sat_iff (p : α → Bool) (a : α) (b : Bool) : p ⊨ (a, b) ↔ (p a) = b := Iff.rfl

theorem sat_negate_iff_not_sat {p : α → Bool} {l : Literal α} : p ⊨ Literal.negate l ↔ p ⊭ l := by
  grind [Literal.negate, sat_iff, cases Bool]

theorem unsat_of_limplies_complement [Entails α t] (x : t) (l : Literal α) :
    Limplies α x l → Limplies α x (Literal.negate l) → Unsatisfiable α x := by
  intro h1 h2 p px
  specialize h1 p px
  specialize h2 p px
  rw [sat_negate_iff_not_sat] at h2
  exact h2 h1

end Literal

namespace Clause

theorem sat_iff_exists [Clause α β] (p : α → Bool) (c : β) : p ⊨ c ↔ ∃ l ∈ toList c, p ⊨ l := by
  simp only [(· ⊨ ·), eval]
  grind [List.any_eq_true]

theorem limplies_iff_mem [DecidableEq α] [Clause α β] (l : Literal α) (c : β) :
    Limplies α l c ↔ l ∈ toList c := by
  simp only [Limplies, sat_iff_exists, Prod.exists, Bool.exists_bool]
  constructor
  · intro h
    -- Construct an assignment p such that p ⊨ l and p ⊭ c ∖ {l}
    let p := fun x : α => if x = l.1 then l.2 else (x, false) ∈ toList c
    have pl : p ⊨ l := by simp only [(· ⊨ ·), ite_true, p]
    specialize h p pl
    rcases h with ⟨v, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
    · simp only [(· ⊨ ·)] at h2
      grind
    · simp only [(· ⊨ ·), p] at h2
      split at h2
      · grind
      · rcases not_tautology c (v, true) <;> grind [Literal.negate]
  · grind [cases Bool]

theorem entails_of_entails_delete [DecidableEq α] [Clause α β] {p : α → Bool} {c : β}
    {l : Literal α} :
    p ⊨ delete c l → p ⊨ c := by
  simp only [(· ⊨ ·), eval] at ⊢
  grind [delete_iff, List.any_eq_true]

end Clause

namespace Formula

theorem sat_iff_forall [Clause α β] [Entails α σ] [Formula α β σ] (p : α → Bool) (f : σ) :
    p ⊨ f ↔ ∀ c : β, c ∈ toList f → p ⊨ c := by
  simp only [formulaEntails_def]
  grind [List.all_eq_true]

theorem limplies_insert [Clause α β] [Entails α σ] [Formula α β σ] {c : β} {f : σ} :
    Limplies α (insert f c) f := by
  intro p
  simp only [formulaEntails_def, List.all_eq_true, decide_eq_true_eq]
  intro h c' c'_in_f
  have c'_in_fc : c' ∈ toList (insert f c) := by grind [insert_iff]
  grind

theorem limplies_delete [Clause α β] [Entails α σ] [Formula α β σ] {f : σ} {arr : Array Nat} :
    Limplies α f (delete f arr) := by
  intro p
  simp only [formulaEntails_def]
  grind [List.all_eq_true, delete_subset]

end Formula

end Internal
end LRAT
end Std.Tactic.BVDecide
