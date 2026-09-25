/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Std.Sat.CNF.Negation
import Init.ByCases

/-!
Formalizations of clause redundancy properties.
-/

public section

namespace Std
namespace Sat

namespace CNF

/-- We may add any tautological clause -/
theorem entails_clause_of_forall_sat {f : CNF α} {c : Clause α} (h : ∀ a, c.Sat a) :
    EntailsClause f c := by
  simp [entails_clause_def, h]

theorem entails_clause_of_unsat_of_forall_not_sat (h1 : ∀ (a : α → Bool), ¬ f1.Sat a → Clause.Sat a c)
    (h2 : CNF.Unsat (f2 ++ f1)) :
    CNF.EntailsClause f2 c := by
  rw [entails_clause_def]
  rw [CNF.unsat_iff_not_sat] at h2
  intro a hf2
  specialize h1 a
  specialize h2 a
  simp_all

/-- This is known as the AT or RUP property. -/
theorem entails_clause_of_unsat_of_isNegationOf (h1 : IsNegationOf f1 c)
    (h2 : CNF.Unsat (f2 ++ f1)) :
    CNF.EntailsClause f2 c := by
  refine entails_clause_of_unsat_of_forall_not_sat ?_ h2
  rw [isNegationOf_def] at h1
  intro a
  simp [h1 a]

open Classical in
/--
This is known as the RAT property. It's a formalization of Proposition 1 from
"Inprocessing Rules" by Matti Järvisalo, Marijn Heule, and Armin Biere
(https://cca.informatik.uni-freiburg.de/papers/JarvisaloHeuleBiere-IJCAR12.pdf)
-/
theorem exists_sat_add_of_rat [BEq α] [LawfulBEq α] {f : CNF α} {c : Clause α} {l : Literal α}
    (h1 : l ∈ c) (h2 : ∀ c' ∈ f, l.negate ∈ c' → f.EntailsClause (c ++ c'.erase l.negate)) :
    ∀ a, f.Sat a → ∃ a', (f.add c).Sat a' := by
  intro a hf
  by_cases hsat1 : c.Sat a
  · exists a
    simp [hf, hsat1]
  · let a' : α → Bool := fun atom => if atom = l.1 then l.2 else a atom
    exists a'
    have hsat2 : c.Sat a' := by
      apply Clause.sat_of_mem_of_eq h1
      simp [a']
    have hsat3 : f.Sat a' := by
      apply sat_of_all_mem_sat
      intro c' hc'
      by_cases hmem1 : l.negate ∈ c'
      · by_cases hmem2 : l ∈ c'
        · apply Clause.sat_of_mem_of_eq hmem2
          simp [a']
        · have hex : ∃ l', l' ∈ c' ∧ l'.1 ≠ l.1 ∧ a l'.1 = l'.2 := by
            have herase : Clause.Sat a (c'.erase l.negate) := by
              specialize h2 c' hc' hmem1
              rw [entails_clause_def] at h2
              specialize h2 a hf
              simpa [hsat1] using h2
            rw [Clause.sat_iff_exists_mem_eq] at herase
            simp only [Clause.mem_erase_iff] at herase
            rcases herase with ⟨l', ⟨hl1', hl2'⟩, hl3'⟩
            exists l'
            refine ⟨hl2', ?_, hl3'⟩
            intro hlit
            rcases l with ⟨atom, pol⟩
            rcases l' with ⟨atom', pol'⟩
            simp_all [Literal.negate]
          rcases hex with ⟨l', hl1', hl2', hl3'⟩
          apply Clause.sat_of_mem_of_eq hl1'
          simp [a', hl2', hl3']
      · rw [sat_iff_all_mem_sat] at hf
        specialize hf c' hc'
        rw [Clause.sat_iff_exists_mem_eq] at hf
        rcases hf with ⟨l', hl1', hl2'⟩
        apply Clause.sat_of_mem_of_eq hl1'
        unfold a'
        split
        · have : l' = l := by
            rcases l with ⟨atom, pol⟩
            rcases l' with ⟨atom', pol'⟩
            cases pol <;> cases pol' <;> simp_all [Literal.negate]
          simp [this]
        · assumption
    simp [hsat2, hsat3]

end CNF

end Sat
end Std
