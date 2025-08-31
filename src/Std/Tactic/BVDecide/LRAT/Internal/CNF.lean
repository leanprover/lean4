/-
Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Clune
-/
module

prelude
public import Std.Tactic.BVDecide.LRAT.Internal.Formula.Class

@[expose] public section

namespace Std.Tactic.BVDecide
namespace LRAT
namespace Internal

open Clause Formula Std Sat

namespace Literal

theorem sat_iff (p : α → Bool) (a : α) (b : Bool) : p ⊨ (a, b) ↔ (p a) = b := Iff.rfl

theorem sat_negate_iff_not_sat {p : α → Bool} {l : Literal α} : p ⊨ Literal.negate l ↔ p ⊭ l := by
  grind [sat_iff, cases Bool]

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
  grind

theorem limplies_iff_mem [DecidableEq α] [Clause α β] (l : Literal α) (c : β) :
    Limplies α l c ↔ l ∈ toList c := by
  simp only [Limplies, sat_iff_exists, Prod.exists, Bool.exists_bool]
  constructor
  · simp only [(· ⊨ ·)]
    intro h
    -- Construct an assignment p such that p ⊨ l and p ⊭ c ∖ {l}
    let p := fun x : α => if x = l.1 then l.2 else (x, false) ∈ toList c
    specialize h p
    grind [not_tautology]
  · grind [cases Bool]

theorem entails_of_entails_delete [DecidableEq α] [Clause α β] {p : α → Bool} {c : β}
    {l : Literal α} :
    p ⊨ delete c l → p ⊨ c := by
  simp only [(· ⊨ ·), eval] at ⊢
  grind

end Clause

namespace Formula

theorem sat_iff_forall [Clause α β] [Entails α σ] [Formula α β σ] (p : α → Bool) (f : σ) :
    p ⊨ f ↔ ∀ c : β, c ∈ toList f → p ⊨ c := by
  simp only [formulaEntails_def]
  grind

theorem limplies_insert [Clause α β] [Entails α σ] [Formula α β σ] {c : β} {f : σ} :
    Limplies α (insert f c) f := by
  simp only [Limplies, formulaEntails_def]
  grind

theorem limplies_delete [Clause α β] [Entails α σ] [Formula α β σ] {f : σ} {arr : Array Nat} :
    Limplies α f (delete f arr) := by
  simp only [Limplies, formulaEntails_def]
  grind

end Formula

end Internal
end LRAT
end Std.Tactic.BVDecide
