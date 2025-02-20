/-
Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Clune
-/
prelude
import Std.Tactic.BVDecide.LRAT.Internal.Formula.Class

namespace Std.Tactic.BVDecide
namespace LRAT
namespace Internal

open Clause Formula Std Sat

namespace Literal

theorem sat_iff (p : α → Bool) (a : α) (b : Bool) : p ⊨ (a, b) ↔ (p a) = b := by
  simp only [Entails.eval]

theorem sat_negate_iff_not_sat {p : α → Bool} {l : Literal α} : p ⊨ Literal.negate l ↔ p ⊭ l := by
  simp only [Literal.negate, sat_iff]
  constructor
  · intro h pl
    rw [sat_iff, h] at pl
    simp at pl
  · intro h
    rw [sat_iff] at h
    cases h : p l.fst <;> simp_all

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
  simp only [List.any_eq_true, decide_eq_true_eq, Prod.exists, Bool.exists_bool]

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
    · simp only [(· ⊨ ·), p] at h2
      split at h2
      · next v_eq_l =>
        cases l
        simp_all
      · next v_ne_l =>
        simp only [decide_eq_false_iff_not] at h2
        exfalso
        exact h2 h1
    · simp only [(· ⊨ ·), p] at h2
      split at h2
      · next v_eq_l =>
        cases l
        simp_all
      · next v_ne_l =>
        simp only [decide_eq_true_eq] at h2
        exfalso
        rcases not_tautology c (v, true) with v_not_in_c | negv_not_in_c
        · exact v_not_in_c h1
        · simp only [Literal.negate, Bool.not_true] at negv_not_in_c
          exact negv_not_in_c h2
  · intro h p pl
    apply Exists.intro l.1
    by_cases hl : l.2
    · apply Or.inr
      rw [← hl]
      exact ⟨h, pl⟩
    · apply Or.inl
      simp only [Bool.not_eq_true] at hl
      rw [← hl]
      exact ⟨h, pl⟩

theorem entails_of_entails_delete [DecidableEq α] [Clause α β] {p : α → Bool} {c : β}
    {l : Literal α} :
    p ⊨ delete c l → p ⊨ c := by
  intro h
  simp only [(· ⊨ ·), eval, List.any_eq_true, decide_eq_true_eq, Prod.exists, Bool.exists_bool] at h
  simp only [(· ⊨ ·), eval, List.any_eq_true, decide_eq_true_eq, Prod.exists, Bool.exists_bool]
  rcases h with ⟨v, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
  · simp only [delete_iff, ne_eq] at h1
    exact Exists.intro v <| Or.inl ⟨h1.2, h2⟩
  · simp only [delete_iff, ne_eq] at h1
    exact Exists.intro v <| Or.inr ⟨h1.2, h2⟩

end Clause

namespace Formula

theorem sat_iff_forall [Clause α β] [Entails α σ] [Formula α β σ] (p : α → Bool) (f : σ) :
    p ⊨ f ↔ ∀ c : β, c ∈ toList f → p ⊨ c := by
  simp only [(· ⊨ ·), formulaEntails_def p f]
  simp only [List.all_eq_true, decide_eq_true_eq]

theorem limplies_insert [Clause α β] [Entails α σ] [Formula α β σ] {c : β} {f : σ} :
    Limplies α (insert f c) f := by
  intro p
  simp only [formulaEntails_def, List.all_eq_true, decide_eq_true_eq]
  intro h c' c'_in_f
  have c'_in_fc : c' ∈ toList (insert f c) := by
    simp only [insert_iff, List.toList_toArray, List.mem_singleton]
    exact Or.inr c'_in_f
  exact h c' c'_in_fc

theorem limplies_delete [Clause α β] [Entails α σ] [Formula α β σ] {f : σ} {arr : Array Nat} :
    Limplies α f (delete f arr) := by
  intro p
  simp only [formulaEntails_def, List.all_eq_true, decide_eq_true_eq]
  intro h c c_in_f_del
  have del_f_subset := delete_subset f arr
  specialize del_f_subset c c_in_f_del
  exact h c del_f_subset

end Formula

end Internal
end LRAT
end Std.Tactic.BVDecide
