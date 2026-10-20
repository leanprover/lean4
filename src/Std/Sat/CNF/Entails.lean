/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Std.Sat.CNF.Sat

public section

namespace Std
namespace Sat

namespace CNF

def Entails (f1 f2 : CNF α) : Prop :=
  ∀ a, Sat a f1 → Sat a f2

def EntailsClause (f : CNF α) (c : Clause α) : Prop :=
  ∀ a, Sat a f → Clause.Sat a c

theorem entails_def (f1 f2 : CNF α) : Entails f1 f2 ↔ ∀ a, Sat a f1 → Sat a f2 := by
  simp [Entails]

@[refl]
theorem entails_refl (f : CNF α) : Entails f f := by
  simp [entails_def]

theorem entails_trans {f1 f2 f3 : CNF α} (h1 : Entails f1 f2) (h2 : Entails f2 f3) :
    Entails f1 f3 := by
  simp_all [entails_def]

theorem entails_clause_def {f : CNF α} {c : Clause α} :
    EntailsClause f c ↔ ∀ a, Sat a f → Clause.Sat a c := by
  simp [EntailsClause]

theorem entails_of_forall_sat (f1 f2 : CNF α) (h : ∀ a, f2.Sat a) :
    Entails f1 f2 := by
  simp [entails_def, h]

theorem entails_add_of_entails_clause (f : CNF α) (c : Clause α) (h : EntailsClause f c) :
    Entails f (f.add c) := by
  rw [entails_def]
  intro a
  rw [entails_clause_def] at h
  specialize h a
  simp only [sat_def, Clause.sat_def] at h
  simp +contextual [sat_def, h]

theorem entails_add_iff {f g : CNF α} {c : Clause α} :
    Entails g (f.add c) ↔ (Entails g f ∧ EntailsClause g c) := by
  rw [entails_def, entails_def, entails_clause_def]
  constructor
  · intro h
    exact ⟨fun a ha => (sat_add.mp (h a ha)).right, fun a ha => (sat_add.mp (h a ha)).left⟩
  · rintro ⟨h1, h2⟩ a ha
    exact sat_add.mpr ⟨h2 a ha, h1 a ha⟩

theorem entails_of_all_mem (f1 f2 : CNF α) (h : ∀ c ∈ f1, c ∈ f2) : Entails f2 f1 := by
  rw [entails_def]
  simp +contextual [sat_iff_all_mem_sat, h]

theorem entails_iff_all_mem_entails_clause {f g : CNF α} :
    Entails f g ↔ ∀ c ∈ g, EntailsClause f c := by
  rw [entails_def]
  constructor
  · intro h c hc a ha
    exact sat_of_mem (h a ha) hc
  · intro h a ha
    exact sat_of_all_mem_sat fun c hc => entails_clause_def.mp (h c hc) a ha

theorem unsat_of_entails_unsat {f1 f2 : CNF α} (h1 : Unsat f2) (h2 : Entails f1 f2) :
    Unsat f1 := by
  simp_all [unsat_iff_not_sat, entails_def]

theorem unsat_of_entails_clause_unsat {f : CNF α} {c : Clause α} (h1 : c.Unsat)
    (h2 : EntailsClause f c) : Unsat f := by
  simp_all [unsat_iff_not_sat, entails_clause_def, Clause.unsat_iff_not_sat]

theorem entails_append_of_entails {f1 f2 f3 : CNF α} (h1 : Entails f1 f2) (h2 : Entails f1 f3) :
    Entails f1 (f2 ++ f3) := by
  simp_all [entails_def]

@[simp]
theorem append_entails_left {f1 f2 : CNF α} :
    Entails (f1 ++ f2) f1 := by
  apply entails_of_all_mem
  simp +contextual

@[simp]
theorem append_entails_right {f1 f2 : CNF α} :
    Entails (f1 ++ f2) f2 := by
  apply entails_of_all_mem
  simp +contextual

theorem entails_append_congr_right {f1 f2 f3 : CNF α} (h1 : Entails f2 f3) :
    Entails (f1 ++ f2) (f1 ++ f3) := by
  apply entails_append_of_entails
  · apply append_entails_left
  · apply entails_trans
    · apply append_entails_right
    · exact h1

theorem entails_append_congr_left {f1 f2 f3 : CNF α} (h1 : Entails f2 f3) :
    Entails (f2 ++ f1) (f3 ++ f1) := by
  apply entails_append_of_entails
  · apply entails_trans
    · apply append_entails_left
    · exact h1
  · apply append_entails_right

theorem entails_append_comm {f1 f2 : CNF α} : Entails (f1 ++ f2) (f2 ++ f1) := by
  apply entails_append_of_entails
  · exact append_entails_right
  · exact append_entails_left

theorem entails_clause_append_iff {f : CNF α} {c1 c2 : Clause α} :
    EntailsClause f (c1 ++ c2) ↔ ∀ a, Sat a f → (Clause.Sat a c1 ∨ Clause.Sat a c2) := by
  simp [entails_clause_def]

theorem entails_clause_append_of_forall {f : CNF α} {c1 c2 : Clause α}
    (h : ∀ a, Sat a f → (Clause.Sat a c1 ∨ Clause.Sat a c2)) : EntailsClause f (c1 ++ c2) :=
  entails_clause_append_iff.mpr h

theorem entails_clause_append_left {f : CNF α} {c1 c2 : Clause α} (h : EntailsClause f c1) :
    EntailsClause f (c1 ++ c2) :=
  entails_clause_append_of_forall fun a ha => Or.inl (entails_clause_def.mp h a ha)

theorem entails_clause_append_right {f : CNF α} {c1 c2 : Clause α} (h : EntailsClause f c2) :
    EntailsClause f (c1 ++ c2) :=
  entails_clause_append_of_forall fun a ha => Or.inr (entails_clause_def.mp h a ha)

theorem entails_clause_append_comm {f : CNF α} {c1 c2 : Clause α} (h : EntailsClause f (c1 ++ c2)) :
    EntailsClause f (c2 ++ c1) :=
  entails_clause_append_of_forall fun a ha => (entails_clause_append_iff.mp h a ha).symm

theorem unsat_of_entails_clause_append_unsat {f : CNF α} {c1 c2 : Clause α}
    (h1 : Clause.Unsat c1) (h2 : Clause.Unsat c2) (h3 : EntailsClause f (c1 ++ c2)) : Unsat f :=
  unsat_of_entails_clause_unsat (Clause.unsat_append.mpr ⟨h1, h2⟩) h3

theorem entails_clause_of_mem {f : CNF α} {c : Clause α} (h : c ∈ f) : EntailsClause f c := by
  rw [entails_clause_def]
  intro a ha
  exact sat_of_mem ha h

@[simp]
theorem add_entails_left {f : CNF α} {c : Clause α} : Entails (f.add c) f := by
  apply entails_of_all_mem
  simp +contextual

@[simp]
theorem entails_clause_add {f : CNF α} {c : Clause α} : EntailsClause (f.add c) c :=
  entails_clause_of_mem (by simp)

theorem entails_clause_trans {f g : CNF α} {c : Clause α} (h1 : Entails f g)
    (h2 : EntailsClause g c) : EntailsClause f c := by
  rw [entails_def] at h1
  rw [entails_clause_def] at h2 ⊢
  intro a ha
  exact h2 a (h1 a ha)

theorem entails_add_congr {f g : CNF α} {c : Clause α} (h : Entails f g) :
    Entails (f.add c) (g.add c) := by
  rw [entails_add_iff]
  exact ⟨entails_trans add_entails_left h, entails_clause_add⟩

@[simp]
theorem entails_empty {f : CNF α} : Entails f .empty := by
  apply entails_of_forall_sat
  simp

theorem unsat_iff_entails_clause_empty {f : CNF α} : Unsat f ↔ EntailsClause f .empty := by
  constructor
  · intro h
    rw [entails_clause_def]
    intro a ha
    exact absurd ha (unsat_iff_not_sat.mp h a)
  · intro h
    exact unsat_of_entails_clause_unsat Clause.unsat_empty h

def BiEntails (f1 f2 : CNF α) : Prop :=
  Entails f1 f2 ∧ Entails f2 f1

theorem biEntails_def : BiEntails f1 f2 ↔ Entails f1 f2 ∧ Entails f2 f1 := by
  simp [BiEntails]

@[refl]
theorem biEntails_refl : BiEntails f f := by
  simp [BiEntails, entails_refl]

theorem biEntails_trans {f1 f2 f3 : CNF α} (h1 : BiEntails f1 f2) (h2 : BiEntails f2 f3) :
    BiEntails f1 f3 := by
  unfold BiEntails at *
  constructor
  · apply entails_trans h1.left h2.left
  · apply entails_trans h2.right h1.right

@[symm]
theorem biEntails_symm (h : BiEntails f1 f2) : BiEntails f2 f1 := by
  rw [biEntails_def] at h ⊢
  exact ⟨h.right, h.left⟩

theorem biEntails_comm : BiEntails f1 f2 ↔ BiEntails f2 f1 :=
  ⟨biEntails_symm, biEntails_symm⟩

end CNF

end Sat
end Std
