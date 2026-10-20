/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Std.Sat.CNF.Basic
public import Std.Sat.CNF.Sat
public import Std.Sat.CNF.Entails
public import Std.Sat.CNF.Unit
import Init.Data.Array.MapIdx

public section

namespace Std
namespace Sat

namespace CNF

def IsNegationOf (f : CNF α) (c : Clause α) : Prop :=
  ∀ a, f.Sat a ↔ ¬c.Sat a

theorem isNegationOf_def : IsNegationOf f c ↔ ∀ a, f.Sat a ↔ ¬c.Sat a := by
  simp [IsNegationOf]

theorem forall_mem_eq_not_of_isNegationOf_of_sat (h1 : IsNegationOf f c) (h2 : Sat a f) :
    ∀ lit ∈ c, a lit.1 = !lit.2 := by
  intro lit hlit
  rw [isNegationOf_def] at h1
  specialize h1 a
  rw [h1] at h2
  rw [Clause.not_sat_iff_forall_mem_ne] at h2
  specialize h2 lit hlit
  cases h : lit.snd <;> simp_all

/--
The negation of `c` as a `CNF`: one unit clause per literal of `c`, with the polarity flipped.
-/
def Clause.negate (c : Clause α) : CNF α :=
  ⟨c.atoms.mapFinIdx fun i atom _ => .unit atom (!(c.polarity i))⟩

@[simp]
theorem Clause.negate_append : Clause.negate (c1 ++ c2) = c1.negate ++ c2.negate := by
  rw [Internal.ext_iff, Internal.clauses_append]
  unfold Clause.negate
  apply Array.ext
  · simp
  · intro i hi1 hi2
    rw [Array.getElem_append]
    split
    · next hlt =>
      have : i < c1.size := by
        simpa [Clause.Internal.size_eq_size_atoms] using hlt
      simp [*, Clause.polarity_append, ← Clause.Internal.size_eq_size_atoms]
    · next hlt =>
      have : ¬i < c1.size := by
        simpa [Clause.Internal.size_eq_size_atoms] using hlt
      have : c1.size ≤ i := by
        simpa [Clause.Internal.size_eq_size_atoms] using hlt
      simp [*, Clause.polarity_append, ← Clause.Internal.size_eq_size_atoms]

@[simp]
theorem Clause.mem_negate_iff {c c' : Clause α} :
    c' ∈ c.negate ↔ ∃ lit ∈ c, c' = unit lit.1 (!lit.2) := by
  simp only [negate, Internal.mem_iff, Array.mem_mapFinIdx]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨(c.atoms[i], c.polarity i), Internal.getElem_mem hi, rfl⟩
  · rintro ⟨lit, hlit, rfl⟩
    rcases Internal.mem_iff_exists_getElem.mp hlit with ⟨i, hi, rfl⟩
    exact ⟨i, hi, rfl⟩

theorem isNegationOf_negate (c : Clause α) : IsNegationOf c.negate c := by
  rw [isNegationOf_def]
  intro a
  rw [sat_iff_all_mem_sat, Clause.not_sat_iff_forall_mem_ne]
  constructor
  · intro h lit hlit
    have hsat := h _ (Clause.mem_negate_iff.mpr ⟨lit, hlit, rfl⟩)
    rw [Clause.sat_unit_iff] at hsat
    simp [hsat]
  · intro h c' hc'
    rcases Clause.mem_negate_iff.mp hc' with ⟨lit, hlit, rfl⟩
    exact Clause.sat_unit_iff.mpr (Bool.eq_not_of_ne (h lit hlit))

theorem Clause.sat_negate_iff_sat_of_isNegationOf (f : CNF α) (h : IsNegationOf f c) :
    ∀ a, CNF.Sat a c.negate ↔ CNF.Sat a f := by
  intro a
  have := isNegationOf_negate c
  rw [isNegationOf_def] at this
  rw [h a]
  apply this

theorem exists_isNegationOf (c : Clause α) : ∃ f, IsNegationOf f c := by
  exists c.negate
  apply isNegationOf_negate

theorem isNegationOf_append_append_of_isNegationOf (h1 : IsNegationOf f1 c1)
    (h2 : IsNegationOf f2 c2) :
    IsNegationOf (f1 ++ f2) (c1 ++ c2) := by
  rw [isNegationOf_def] at h1 h2 ⊢
  intro a
  rw [sat_append, Clause.sat_append, h1 a, h2 a, not_or]

theorem isNegationOf_of_isNegationOf_of_biEntails (h1 : IsNegationOf f1 c) (h2 : BiEntails f1 f2) :
    IsNegationOf f2 c := by
  rw [isNegationOf_def] at h1 ⊢
  rw [biEntails_def, entails_def, entails_def] at h2
  intro a
  rw [← h1 a]
  exact ⟨h2.right a, h2.left a⟩

theorem isNegationOf_append_comm_left : IsNegationOf (f1 ++ f2) c ↔ IsNegationOf (f2 ++ f1) c :=
  ⟨fun h => isNegationOf_of_isNegationOf_of_biEntails h
      (biEntails_def.mpr ⟨entails_append_comm, entails_append_comm⟩),
    fun h => isNegationOf_of_isNegationOf_of_biEntails h
      (biEntails_def.mpr ⟨entails_append_comm, entails_append_comm⟩)⟩

theorem isNegationOf_append_comm_right : IsNegationOf f (c1 ++ c2) ↔ IsNegationOf f (c2 ++ c1) := by
  rw [isNegationOf_def, isNegationOf_def]
  simp only [Clause.sat_append]
  constructor <;> (intro h a; rw [h a]; simp [or_comm])

end CNF

end Sat
end Std
