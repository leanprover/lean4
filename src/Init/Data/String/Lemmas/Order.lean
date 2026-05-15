/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Markus Himmel
-/
module

prelude
public import Init.Data.String.Basic
import Init.Data.String.OrderInstances
import Init.Data.String.Lemmas.Basic
import Init.Data.Order.Lemmas
import Init.Omega
import Init.ByCases

public section

namespace String

@[simp]
theorem Slice.Pos.next_le_iff_lt {s : Slice} {p q : s.Pos} {h} : p.next h ≤ q ↔ p < q :=
  ⟨fun h => Std.lt_of_lt_of_le lt_next h, next_le_of_lt⟩

@[simp]
theorem Slice.Pos.lt_next_iff_le {s : Slice} {p q : s.Pos} {h} : p < q.next h ↔ p ≤ q := by
  rw [← Decidable.not_iff_not, Std.not_lt, next_le_iff_lt, Std.not_le]

theorem Slice.Pos.next_eq_iff {s : Slice} {p q : s.Pos} {h} :
    p.next h = q ↔ p < q ∧ ∀ (q' : s.Pos), p < q' → q ≤ q' :=
  ⟨by rintro rfl; simp, fun ⟨h₁, h₂⟩ => Std.le_antisymm (by simpa) (h₂ _ (by simp))⟩

@[simp]
theorem Pos.next_le_iff_lt {s : String} {p q : s.Pos} {h} : p.next h ≤ q ↔ p < q := by
  rw [next, Pos.ofToSlice_le_iff, ← Pos.toSlice_lt_toSlice_iff]
  exact Slice.Pos.next_le_iff_lt

@[simp]
theorem Pos.lt_next_iff_le {s : String} {p q : s.Pos} {h} : p < q.next h ↔ p ≤ q := by
  rw [← Std.not_le, next_le_iff_lt, Std.not_lt]

theorem Pos.next_eq_iff {s : String} {p q : s.Pos} {h} :
    p.next h = q ↔ p < q ∧ ∀ (q' : s.Pos), p < q' → q ≤ q' :=
  ⟨by rintro rfl; simp, fun ⟨h₁, h₂⟩ => Std.le_antisymm (by simpa) (h₂ _ (by simp))⟩

@[simp]
theorem Slice.Pos.le_startPos {s : Slice} (p : s.Pos) : p ≤ s.startPos ↔ p = s.startPos :=
  ⟨fun h => Std.le_antisymm h (startPos_le _), by simp +contextual⟩

@[simp]
theorem Slice.Pos.startPos_lt_iff {s : Slice} (p : s.Pos) : s.startPos < p ↔ p ≠ s.startPos := by
  simp [← le_startPos, Std.not_le]

@[simp]
theorem Slice.Pos.endPos_le {s : Slice} (p : s.Pos) : s.endPos ≤ p ↔ p = s.endPos :=
  ⟨fun h => Std.le_antisymm (le_endPos _) h, by simp +contextual⟩

@[simp]
theorem Slice.Pos.lt_endPos_iff {s : Slice} (p : s.Pos) : p < s.endPos ↔ p ≠ s.endPos := by
  simp [← endPos_le, Std.not_le]

@[simp]
theorem Pos.endPos_le {s : String} (p : s.Pos) : s.endPos ≤ p ↔ p = s.endPos :=
  ⟨fun h => Std.le_antisymm (le_endPos _) h, by simp +contextual⟩

@[simp]
theorem Pos.lt_endPos_iff {s : String} (p : s.Pos) : p < s.endPos ↔ p ≠ s.endPos := by
  simp [← endPos_le, Std.not_le]

@[simp]
theorem Pos.le_startPos {s : String} (p : s.Pos) : p ≤ s.startPos ↔ p = s.startPos :=
  ⟨fun h => Std.le_antisymm h (startPos_le _), by simp +contextual⟩

@[simp]
theorem Pos.startPos_lt_iff {s : String} (p : s.Pos) : s.startPos < p ↔ p ≠ s.startPos := by
  simp [← le_startPos, Std.not_le]

@[simp]
theorem Slice.Pos.not_lt_startPos {s : Slice} {p : s.Pos} : ¬ p < s.startPos :=
  fun h => Std.lt_irrefl (Std.lt_of_lt_of_le h (Slice.Pos.startPos_le _))

theorem Slice.Pos.ne_startPos_of_lt {s : Slice} {p q : s.Pos} : p < q → q ≠ s.startPos := by
  rintro h rfl
  simp at h

@[simp]
theorem Pos.not_lt_startPos {s : String} {p : s.Pos} : ¬ p < s.startPos :=
  fun h => Std.lt_irrefl (Std.lt_of_lt_of_le h (Pos.startPos_le _))

@[simp]
theorem Slice.Pos.not_endPos_lt {s : Slice} {p : s.Pos} : ¬ s.endPos < p :=
  fun h => Std.lt_irrefl (Std.lt_of_le_of_lt (Slice.Pos.le_endPos _) h)

@[simp]
theorem Pos.not_endPos_lt {s : String} {p : s.Pos} : ¬ s.endPos < p :=
  fun h => Std.lt_irrefl (Std.lt_of_le_of_lt (Pos.le_endPos _) h)

theorem Pos.ne_endPos_of_lt {s : String} {p q : s.Pos} : p < q → p ≠ s.endPos := by
  rintro h rfl
  simp at h

@[simp]
theorem Slice.Pos.le_next {s : Slice} {p : s.Pos} {h} : p ≤ p.next h :=
  Std.le_of_lt (by simp)

@[simp]
theorem Pos.le_next {s : String} {p : s.Pos} {h} : p ≤ p.next h :=
  Std.le_of_lt (by simp)

@[simp]
theorem Slice.Pos.ne_next {s : Slice} {p : s.Pos} {h} : p ≠ p.next h :=
  Std.ne_of_lt (by simp)

@[simp]
theorem Pos.ne_next {s : String} {p : s.Pos} {h} : p ≠ p.next h :=
  Std.ne_of_lt (by simp)

@[simp]
theorem Slice.Pos.next_ne {s : Slice} {p : s.Pos} {h} : p.next h ≠ p :=
  Ne.symm (by simp)

@[simp]
theorem Pos.next_ne {s : String} {p : s.Pos} {h} : p.next h ≠ p :=
  Ne.symm (by simp)

@[simp]
theorem Slice.Pos.next_ne_startPos {s : Slice} {p : s.Pos} {h} :
    p.next h ≠ s.startPos :=
  ne_startPos_of_lt lt_next

@[simp]
theorem Slice.Pos.ofSliceTo_lt_ofSliceTo_iff {s : Slice} {p : s.Pos}
    {q r : (s.sliceTo p).Pos} : Slice.Pos.ofSliceTo q < Slice.Pos.ofSliceTo r ↔ q < r := by
  simp [Slice.Pos.lt_iff, Pos.Raw.lt_iff]

@[simp]
theorem Slice.Pos.ofSliceTo_le_ofSliceTo_iff {s : Slice} {p : s.Pos}
    {q r : (s.sliceTo p).Pos} : Slice.Pos.ofSliceTo q ≤ Slice.Pos.ofSliceTo r ↔ q ≤ r := by
  simp [Slice.Pos.le_iff, Pos.Raw.le_iff]

@[simp]
theorem Slice.Pos.sliceTo_lt_sliceTo_iff {s : Slice} {p₀ : s.Pos} {q r : s.Pos} {h₁ h₂} :
    Pos.sliceTo p₀ q h₁ < Pos.sliceTo p₀ r h₂ ↔ q < r := by
  simp [Slice.Pos.lt_iff, Pos.Raw.lt_iff]

@[simp]
theorem Slice.Pos.sliceTo_le_sliceTo_iff {s : Slice} {p₀ : s.Pos} {q r : s.Pos} {h₁ h₂} :
    Pos.sliceTo p₀ q h₁ ≤ Pos.sliceTo p₀ r h₂ ↔ q ≤ r := by
  simp [Slice.Pos.le_iff, Pos.Raw.le_iff]

@[simp]
theorem Pos.sliceTo_lt_sliceTo_iff {s : String} {p₀ : s.Pos} {q r : s.Pos} {h₁ h₂} :
    Pos.sliceTo p₀ q h₁ < Pos.sliceTo p₀ r h₂ ↔ q < r := by
  simp [Slice.Pos.lt_iff, Pos.lt_iff, Pos.Raw.lt_iff]

@[simp]
theorem Pos.sliceTo_le_sliceTo_iff {s : String} {p₀ : s.Pos} {q r : s.Pos} {h₁ h₂} :
    Pos.sliceTo p₀ q h₁ ≤ Pos.sliceTo p₀ r h₂ ↔ q ≤ r := by
  simp [Slice.Pos.le_iff, Pos.le_iff, Pos.Raw.le_iff]

@[simp]
theorem Slice.Pos.sliceFrom_lt_sliceFrom_iff {s : Slice} {p₀ : s.Pos} {q r : s.Pos} {h₁ h₂} :
    Pos.sliceFrom p₀ q h₁ < Pos.sliceFrom p₀ r h₂ ↔ q < r := by
  simp [Slice.Pos.lt_iff, Pos.Raw.lt_iff, Slice.Pos.le_iff, Pos.Raw.le_iff] at h₁ h₂ ⊢
  omega

@[simp]
theorem Slice.Pos.sliceFrom_le_sliceFrom_iff {s : Slice} {p₀ : s.Pos} {q r : s.Pos} {h₁ h₂} :
    Pos.sliceFrom p₀ q h₁ ≤ Pos.sliceFrom p₀ r h₂ ↔ q ≤ r := by
  simp [Slice.Pos.le_iff, Pos.Raw.le_iff] at h₁ h₂ ⊢
  omega

@[simp]
theorem Pos.sliceFrom_lt_sliceFrom_iff {s : String} {p₀ : s.Pos} {q r : s.Pos} {h₁ h₂} :
    Pos.sliceFrom p₀ q h₁ < Pos.sliceFrom p₀ r h₂ ↔ q < r := by
  simp [Slice.Pos.lt_iff, Pos.lt_iff, Pos.Raw.lt_iff, Pos.le_iff, Pos.Raw.le_iff] at h₁ h₂ ⊢
  omega

@[simp]
theorem Pos.sliceFrom_le_sliceFrom_iff {s : String} {p₀ : s.Pos} {q r : s.Pos} {h₁ h₂} :
    Pos.sliceFrom p₀ q h₁ ≤ Pos.sliceFrom p₀ r h₂ ↔ q ≤ r := by
  simp [Slice.Pos.le_iff, Pos.le_iff, Pos.Raw.le_iff] at h₁ h₂ ⊢
  omega

theorem Slice.Pos.ofSliceFrom_lt_iff {s : Slice} {p₀ : s.Pos} {p : (s.sliceFrom p₀).Pos} {q : s.Pos} :
    Pos.ofSliceFrom p < q ↔ ∃ h, p < Slice.Pos.sliceFrom p₀ q h := by
  refine ⟨fun h => ⟨Std.le_of_lt (Std.lt_of_le_of_lt Pos.le_ofSliceFrom h), ?_⟩, fun ⟨h, h'⟩ => ?_⟩
  · simp +singlePass only [← Pos.sliceFrom_ofSliceFrom (p := p)]
    rwa [Pos.sliceFrom_lt_sliceFrom_iff]
  · simp +singlePass only [← Pos.ofSliceFrom_sliceFrom (h := h)]
    rwa [Pos.ofSliceFrom_lt_ofSliceFrom_iff]

theorem Slice.Pos.le_ofSliceFrom_iff {s : Slice} {p₀ : s.Pos} {p : (s.sliceFrom p₀).Pos} {q : s.Pos} :
    q ≤ Pos.ofSliceFrom p ↔ ∀ h, Slice.Pos.sliceFrom p₀ q h ≤ p := by
  simp [← Std.not_lt, Pos.ofSliceFrom_lt_iff]

theorem Slice.Pos.ofSliceFrom_le_iff {s : Slice} {p₀ : s.Pos} {p : (s.sliceFrom p₀).Pos} {q : s.Pos} :
    Pos.ofSliceFrom p ≤ q ↔ ∃ h, p ≤ Slice.Pos.sliceFrom p₀ q h := by
  refine ⟨fun h => ⟨Std.le_trans Pos.le_ofSliceFrom h, ?_⟩, fun ⟨h, h'⟩ => ?_⟩
  · simp +singlePass only [← Pos.sliceFrom_ofSliceFrom (p := p)]
    rwa [Pos.sliceFrom_le_sliceFrom_iff]
  · simp +singlePass only [← Pos.ofSliceFrom_sliceFrom (h := h)]
    rwa [Pos.ofSliceFrom_le_ofSliceFrom_iff]

theorem Slice.Pos.lt_ofSliceFrom_iff {s : Slice} {p₀ : s.Pos} {p : (s.sliceFrom p₀).Pos} {q : s.Pos} :
    q < Pos.ofSliceFrom p ↔ ∀ h, Slice.Pos.sliceFrom p₀ q h < p := by
  simp [← Std.not_le, Pos.ofSliceFrom_le_iff]

theorem Pos.ofSliceFrom_lt_iff {s : String} {p₀ : s.Pos} {p : (s.sliceFrom p₀).Pos} {q : s.Pos} :
    Pos.ofSliceFrom p < q ↔ ∃ h, p < Pos.sliceFrom p₀ q h := by
  refine ⟨fun h => ⟨Std.le_of_lt (Std.lt_of_le_of_lt Pos.le_ofSliceFrom h), ?_⟩, fun ⟨h, h'⟩ => ?_⟩
  · simp +singlePass only [← Pos.sliceFrom_ofSliceFrom (p := p)]
    rwa [Pos.sliceFrom_lt_sliceFrom_iff]
  · simp +singlePass only [← Pos.ofSliceFrom_sliceFrom (h := h)]
    rwa [Pos.ofSliceFrom_lt_ofSliceFrom_iff]

theorem Pos.le_ofSliceFrom_iff {s : String} {p₀ : s.Pos} {p : (s.sliceFrom p₀).Pos} {q : s.Pos} :
    q ≤ Pos.ofSliceFrom p ↔ ∀ h, Pos.sliceFrom p₀ q h ≤ p := by
  simp [← Std.not_lt, Pos.ofSliceFrom_lt_iff]

theorem Pos.ofSliceFrom_le_iff {s : String} {p₀ : s.Pos} {p : (s.sliceFrom p₀).Pos} {q : s.Pos} :
    Pos.ofSliceFrom p ≤ q ↔ ∃ h, p ≤ Pos.sliceFrom p₀ q h := by
  refine ⟨fun h => ⟨Std.le_trans Pos.le_ofSliceFrom h, ?_⟩, fun ⟨h, h'⟩ => ?_⟩
  · simp +singlePass only [← Pos.sliceFrom_ofSliceFrom (p := p)]
    rwa [Pos.sliceFrom_le_sliceFrom_iff]
  · simp +singlePass only [← Pos.ofSliceFrom_sliceFrom (h := h)]
    rwa [Pos.ofSliceFrom_le_ofSliceFrom_iff]

theorem Pos.lt_ofSliceFrom_iff {s : String} {p₀ : s.Pos} {p : (s.sliceFrom p₀).Pos} {q : s.Pos} :
    q < Pos.ofSliceFrom p ↔ ∀ h, Pos.sliceFrom p₀ q h < p := by
  simp [← Std.not_le, Pos.ofSliceFrom_le_iff]

theorem Slice.Pos.ofSliceFrom_next {s : Slice} {p₀ : s.Pos} {p : (s.sliceFrom p₀).Pos} {h} :
    Pos.ofSliceFrom (p.next h) = (Pos.ofSliceFrom p).next (by simpa [← Pos.ofSliceFrom_inj] using h) := by
  rw [eq_comm, Pos.next_eq_iff]
  simp only [Pos.ofSliceFrom_lt_ofSliceFrom_iff, Pos.lt_next, Pos.ofSliceFrom_le_iff,
    Pos.next_le_iff_lt, true_and]
  simp [Pos.ofSliceFrom_lt_iff]

theorem Slice.Pos.next_ofSliceFrom {s : Slice} {p₀ : s.Pos} {p : (s.sliceFrom p₀).Pos} {h} :
    (Pos.ofSliceFrom p).next h = Pos.ofSliceFrom (p.next (by simpa [← Pos.ofSliceFrom_inj])) := by
  simp [ofSliceFrom_next]

theorem Pos.ofSliceFrom_next {s : String} {p₀ : s.Pos} {p : (s.sliceFrom p₀).Pos} {h} :
    Pos.ofSliceFrom (p.next h) = (Pos.ofSliceFrom p).next (by simpa [← Pos.ofSliceFrom_inj] using h) := by
  rw [eq_comm, Pos.next_eq_iff]
  simp only [Pos.ofSliceFrom_lt_ofSliceFrom_iff, Slice.Pos.lt_next, Pos.ofSliceFrom_le_iff,
    Slice.Pos.next_le_iff_lt, true_and]
  simp [Pos.ofSliceFrom_lt_iff]

theorem Pos.next_ofSliceFrom {s : String} {p₀ : s.Pos} {p : (s.sliceFrom p₀).Pos} {h} :
    (Pos.ofSliceFrom p).next h = Pos.ofSliceFrom (p.next (by simpa [← Pos.ofSliceFrom_inj])) := by
  simp [Pos.ofSliceFrom_next]

theorem Slice.Pos.le_ofSliceTo_iff {s : Slice} {p₀ : s.Pos} {p : (s.sliceTo p₀).Pos} {q : s.Pos} :
    q ≤ Pos.ofSliceTo p ↔ ∃ h, Slice.Pos.sliceTo p₀ q h ≤ p := by
  refine ⟨fun h => ⟨Slice.Pos.le_trans h Pos.ofSliceTo_le, ?_⟩, fun ⟨h, h'⟩ => ?_⟩
  · simp +singlePass only [← Pos.sliceTo_ofSliceTo (p := p)]
    rwa [Pos.sliceTo_le_sliceTo_iff]
  · simp +singlePass only [← Pos.ofSliceTo_sliceTo (h := h)]
    rwa [Pos.ofSliceTo_le_ofSliceTo_iff]

theorem Slice.Pos.ofSliceTo_lt_iff {s : Slice} {p₀ : s.Pos} {p : (s.sliceTo p₀).Pos} {q : s.Pos} :
    Pos.ofSliceTo p < q ↔ ∀ h, p < Slice.Pos.sliceTo p₀ q h := by
  simp [← Std.not_le, Slice.Pos.le_ofSliceTo_iff]

theorem Slice.Pos.lt_ofSliceTo_iff {s : Slice} {p₀ : s.Pos} {p : (s.sliceTo p₀).Pos} {q : s.Pos} :
    q < Pos.ofSliceTo p ↔ ∃ h, Slice.Pos.sliceTo p₀ q h < p := by
  refine ⟨fun h => ⟨Std.le_of_lt (Std.lt_of_le_of_lt (Std.le_refl q) (Std.lt_of_lt_of_le h Pos.ofSliceTo_le)), ?_⟩, fun ⟨h, h'⟩ => ?_⟩
  · simp +singlePass only [← Pos.sliceTo_ofSliceTo (p := p)]
    rwa [Pos.sliceTo_lt_sliceTo_iff]
  · simp +singlePass only [← Pos.ofSliceTo_sliceTo (h := h)]
    rwa [Pos.ofSliceTo_lt_ofSliceTo_iff]

theorem Slice.Pos.ofSliceTo_le_iff {s : Slice} {p₀ : s.Pos} {p : (s.sliceTo p₀).Pos} {q : s.Pos} :
    Pos.ofSliceTo p ≤ q ↔ ∀ h, p ≤ Slice.Pos.sliceTo p₀ q h := by
  simp [← Std.not_lt, Slice.Pos.lt_ofSliceTo_iff]

theorem Pos.le_ofSliceTo_iff {s : String} {p₀ : s.Pos} {p : (s.sliceTo p₀).Pos} {q : s.Pos} :
    q ≤ Pos.ofSliceTo p ↔ ∃ h, Pos.sliceTo p₀ q h ≤ p := by
  refine ⟨fun h => ⟨Pos.le_trans h Pos.ofSliceTo_le, ?_⟩, fun ⟨h, h'⟩ => ?_⟩
  · simp +singlePass only [← Pos.sliceTo_ofSliceTo (p := p)]
    rwa [Pos.sliceTo_le_sliceTo_iff]
  · simp +singlePass only [← Pos.ofSliceTo_sliceTo (h := h)]
    rwa [Pos.ofSliceTo_le_ofSliceTo_iff]

theorem Pos.ofSliceTo_lt_iff {s : String} {p₀ : s.Pos} {p : (s.sliceTo p₀).Pos} {q : s.Pos} :
    Pos.ofSliceTo p < q ↔ ∀ h, p < Pos.sliceTo p₀ q h := by
  simp [← Std.not_le, Pos.le_ofSliceTo_iff]

theorem Pos.lt_ofSliceTo_iff {s : String} {p₀ : s.Pos} {p : (s.sliceTo p₀).Pos} {q : s.Pos} :
    q < Pos.ofSliceTo p ↔ ∃ h, Pos.sliceTo p₀ q h < p := by
  refine ⟨fun h => ⟨Pos.le_of_lt (Pos.lt_of_lt_of_le h Pos.ofSliceTo_le), ?_⟩, fun ⟨h, h'⟩ => ?_⟩
  · simp +singlePass only [← Pos.sliceTo_ofSliceTo (p := p)]
    rwa [Pos.sliceTo_lt_sliceTo_iff]
  · simp +singlePass only [← Pos.ofSliceTo_sliceTo (h := h)]
    rwa [Pos.ofSliceTo_lt_ofSliceTo_iff]

theorem Pos.ofSliceTo_le_iff {s : String} {p₀ : s.Pos} {p : (s.sliceTo p₀).Pos} {q : s.Pos} :
    Pos.ofSliceTo p ≤ q ↔ ∀ h, p ≤ Pos.sliceTo p₀ q h := by
  simp [← Std.not_lt, Pos.lt_ofSliceTo_iff]

theorem Slice.Pos.lt_sliceFrom_iff {s : Slice} {p₀ : s.Pos} {p : (s.sliceFrom p₀).Pos} {q : s.Pos} {h} :
    p < Slice.Pos.sliceFrom p₀ q h ↔ Pos.ofSliceFrom p < q := by
  simp [ofSliceFrom_lt_iff, h]

theorem Slice.Pos.sliceFrom_le_iff {s : Slice} {p₀ : s.Pos} {p : (s.sliceFrom p₀).Pos} {q : s.Pos} {h} :
    Slice.Pos.sliceFrom p₀ q h ≤ p ↔ q ≤ Pos.ofSliceFrom p := by
  simp [← Std.not_lt, lt_sliceFrom_iff]

theorem Slice.Pos.le_sliceFrom_iff {s : Slice} {p₀ : s.Pos} {p : (s.sliceFrom p₀).Pos} {q : s.Pos} {h} :
    p ≤ Slice.Pos.sliceFrom p₀ q h ↔ Pos.ofSliceFrom p ≤ q := by
  simp [ofSliceFrom_le_iff, h]

theorem Slice.Pos.sliceFrom_lt_iff {s : Slice} {p₀ : s.Pos} {p : (s.sliceFrom p₀).Pos} {q : s.Pos} {h} :
    Slice.Pos.sliceFrom p₀ q h < p ↔ q < Pos.ofSliceFrom p := by
  simp [← Std.not_le, le_sliceFrom_iff]

theorem Pos.lt_sliceFrom_iff {s : String} {p₀ : s.Pos} {p : (s.sliceFrom p₀).Pos} {q : s.Pos} {h} :
    p < Pos.sliceFrom p₀ q h ↔ Pos.ofSliceFrom p < q := by
  simp [ofSliceFrom_lt_iff, h]

theorem Pos.sliceFrom_le_iff {s : String} {p₀ : s.Pos} {p : (s.sliceFrom p₀).Pos} {q : s.Pos} {h} :
    Pos.sliceFrom p₀ q h ≤ p ↔ q ≤ Pos.ofSliceFrom p := by
  simp [← Std.not_lt, lt_sliceFrom_iff]

theorem Pos.le_sliceFrom_iff {s : String} {p₀ : s.Pos} {p : (s.sliceFrom p₀).Pos} {q : s.Pos} {h} :
    p ≤ Pos.sliceFrom p₀ q h ↔ Pos.ofSliceFrom p ≤ q := by
  simp [ofSliceFrom_le_iff, h]

theorem Pos.sliceFrom_lt_iff {s : String} {p₀ : s.Pos} {p : (s.sliceFrom p₀).Pos} {q : s.Pos} {h} :
    Pos.sliceFrom p₀ q h < p ↔ q < Pos.ofSliceFrom p := by
  simp [← Std.not_le, le_sliceFrom_iff]

theorem Slice.Pos.sliceTo_le_iff {s : Slice} {p₀ : s.Pos} {p : (s.sliceTo p₀).Pos} {q : s.Pos} {h} :
    Pos.sliceTo p₀ q h ≤ p ↔ q ≤ Pos.ofSliceTo p := by
  simp [le_ofSliceTo_iff, h]

theorem Slice.Pos.lt_sliceTo_iff {s : Slice} {p₀ : s.Pos} {p : (s.sliceTo p₀).Pos} {q : s.Pos} {h} :
    p < Pos.sliceTo p₀ q h ↔ Pos.ofSliceTo p < q := by
  simp [← Std.not_le, sliceTo_le_iff]

theorem Slice.Pos.sliceTo_lt_iff {s : Slice} {p₀ : s.Pos} {p : (s.sliceTo p₀).Pos} {q : s.Pos} {h} :
    Slice.Pos.sliceTo p₀ q h < p ↔ q < Pos.ofSliceTo p := by
  simp [lt_ofSliceTo_iff, h]

theorem Slice.Pos.le_sliceTo_iff {s : Slice} {p₀ : s.Pos} {p : (s.sliceTo p₀).Pos} {q : s.Pos} {h} :
    p ≤ Slice.Pos.sliceTo p₀ q h ↔ Pos.ofSliceTo p ≤ q := by
  simp [← Std.not_lt, sliceTo_lt_iff]

theorem Pos.sliceTo_le_iff {s : String} {p₀ : s.Pos} {p : (s.sliceTo p₀).Pos} {q : s.Pos} {h} :
    Pos.sliceTo p₀ q h ≤ p ↔ q ≤ Pos.ofSliceTo p := by
  simp [le_ofSliceTo_iff, h]

theorem Pos.lt_sliceTo_iff {s : String} {p₀ : s.Pos} {p : (s.sliceTo p₀).Pos} {q : s.Pos} {h} :
    p < Pos.sliceTo p₀ q h ↔ Pos.ofSliceTo p < q := by
  simp [← Std.not_le, sliceTo_le_iff]

theorem Pos.sliceTo_lt_iff {s : String} {p₀ : s.Pos} {p : (s.sliceTo p₀).Pos} {q : s.Pos} {h} :
    Pos.sliceTo p₀ q h < p ↔ q < Pos.ofSliceTo p := by
  simp [lt_ofSliceTo_iff, h]

theorem Pos.le_sliceTo_iff {s : String} {p₀ : s.Pos} {p : (s.sliceTo p₀).Pos} {q : s.Pos} {h} :
    p ≤ Pos.sliceTo p₀ q h ↔ Pos.ofSliceTo p ≤ q := by
  simp [← Std.not_lt, sliceTo_lt_iff]

theorem Slice.Pos.ofSliceTo_ne_endPos {s : Slice} {p₀ : s.Pos} {p : (s.sliceTo p₀).Pos}
    (h : p ≠ (s.sliceTo p₀).endPos) : Pos.ofSliceTo p ≠ s.endPos := by
  refine (lt_endPos_iff _).1 (Std.lt_of_lt_of_le ?_ (le_endPos p₀))
  simpa [← lt_endPos_iff, ← ofSliceTo_lt_ofSliceTo_iff] using h

theorem Slice.Pos.ne_endPos_of_sliceTo_ne_endPos {s : Slice} {p p₀ : s.Pos} {h₀}
    (h : Pos.sliceTo p₀ p h₀ ≠ Slice.endPos _) : p ≠ s.endPos := by
  rw [← Pos.ofSliceTo_sliceTo (h := h₀)]
  apply Pos.ofSliceTo_ne_endPos h

theorem Slice.Pos.ofSliceFrom_ne_startPos {s : Slice} {p₀ : s.Pos} {p : (s.sliceFrom p₀).Pos}
    (h : p ≠ (s.sliceFrom p₀).startPos) : Pos.ofSliceFrom p ≠ s.startPos := by
  refine (startPos_lt_iff _).1 (Std.lt_of_le_of_lt (startPos_le p₀) ?_)
  simpa [← startPos_lt_iff, ← ofSliceFrom_lt_ofSliceFrom_iff] using h

theorem Slice.Pos.ne_startPos_of_sliceFrom_ne_startPos {s : Slice} {p p₀ : s.Pos} {h₀}
    (h : Pos.sliceFrom p₀ p h₀ ≠ Slice.startPos _) : p ≠ s.startPos := by
  rw [← Pos.ofSliceFrom_sliceFrom (h := h₀)]
  apply Pos.ofSliceFrom_ne_startPos h

theorem Pos.ofSliceTo_ne_endPos {s : String} {p₀ : s.Pos} {p : (s.sliceTo p₀).Pos}
    (h : p ≠ (s.sliceTo p₀).endPos) : Pos.ofSliceTo p ≠ s.endPos := by
  refine (lt_endPos_iff _).1 (Std.lt_of_lt_of_le ?_ (le_endPos p₀))
  simpa [← Slice.Pos.lt_endPos_iff, ← ofSliceTo_lt_ofSliceTo_iff] using h

theorem Pos.ne_endPos_of_sliceTo_ne_endPos {s : String} {p p₀ : s.Pos} {h₀}
    (h : Pos.sliceTo p₀ p h₀ ≠ Slice.endPos _) : p ≠ s.endPos := by
  rw [← Pos.ofSliceTo_sliceTo (h := h₀)]
  apply Pos.ofSliceTo_ne_endPos h

theorem Pos.ofSliceFrom_ne_startPos {s : String} {p₀ : s.Pos} {p : (s.sliceFrom p₀).Pos}
    (h : p ≠ (s.sliceFrom p₀).startPos) : Pos.ofSliceFrom p ≠ s.startPos := by
  refine (startPos_lt_iff _).1 (Std.lt_of_le_of_lt (startPos_le p₀) ?_)
  simpa [← Slice.Pos.startPos_lt_iff, ← ofSliceFrom_lt_ofSliceFrom_iff] using h

theorem Pos.ne_startPos_of_sliceFrom_ne_startPos {s : String} {p p₀ : s.Pos} {h₀}
    (h : Pos.sliceFrom p₀ p h₀ ≠ Slice.startPos _) : p ≠ s.startPos := by
  rw [← Pos.ofSliceFrom_sliceFrom (h := h₀)]
  apply Pos.ofSliceFrom_ne_startPos h

theorem Slice.Pos.ofSliceTo_next {s : Slice} {p₀ : s.Pos} {p : (s.sliceTo p₀).Pos} {h} :
    Pos.ofSliceTo (p.next h) = (Pos.ofSliceTo p).next (ofSliceTo_ne_endPos h) := by
  rw [eq_comm, Pos.next_eq_iff]
  simp only [Pos.ofSliceTo_lt_ofSliceTo_iff, Pos.lt_next, Pos.ofSliceTo_le_iff,
    Pos.next_le_iff_lt, true_and]
  simp [Pos.ofSliceTo_lt_iff]

theorem Pos.ofSliceTo_next {s : String} {p₀ : s.Pos} {p : (s.sliceTo p₀).Pos} {h} :
    Pos.ofSliceTo (p.next h) = (Pos.ofSliceTo p).next (ofSliceTo_ne_endPos h) := by
  rw [eq_comm, Pos.next_eq_iff]
  simp only [Pos.ofSliceTo_lt_ofSliceTo_iff, Slice.Pos.lt_next, Pos.ofSliceTo_le_iff,
    Slice.Pos.next_le_iff_lt, true_and]
  simp [Pos.ofSliceTo_lt_iff]

@[simp]
theorem Slice.Pos.slice_lt_slice_iff {s : Slice} {p₀ p₁ : s.Pos} {q r : s.Pos}
    {h₁ h₁' h₂ h₂'} :
    q.slice p₀ p₁ h₁ h₂ < r.slice p₀ p₁ h₁' h₂' ↔ q < r := by
  simp [Slice.Pos.lt_iff, Pos.Raw.lt_iff, Slice.Pos.le_iff, Pos.Raw.le_iff] at h₁ h₁' ⊢
  omega

@[simp]
theorem Slice.Pos.slice_le_slice_iff {s : Slice} {p₀ p₁ : s.Pos} {q r : s.Pos}
    {h₁ h₁' h₂ h₂'} :
    q.slice p₀ p₁ h₁ h₂ ≤ r.slice p₀ p₁ h₁' h₂' ↔ q ≤ r := by
  simp [Slice.Pos.le_iff, Pos.Raw.le_iff] at h₁ h₁' ⊢
  omega

@[simp]
theorem Pos.slice_lt_slice_iff {s : String} {p₀ p₁ : s.Pos} {q r : s.Pos}
    {h₁ h₁' h₂ h₂'} :
    q.slice p₀ p₁ h₁ h₂ < r.slice p₀ p₁ h₁' h₂' ↔ q < r := by
  simp [Slice.Pos.lt_iff, Pos.lt_iff, Pos.Raw.lt_iff, Pos.le_iff, Pos.Raw.le_iff] at h₁ h₁' ⊢
  omega

@[simp]
theorem Pos.slice_le_slice_iff {s : String} {p₀ p₁ : s.Pos} {q r : s.Pos}
    {h₁ h₁' h₂ h₂'} :
    q.slice p₀ p₁ h₁ h₂ ≤ r.slice p₀ p₁ h₁' h₂' ↔ q ≤ r := by
  simp [Slice.Pos.le_iff, Pos.le_iff, Pos.Raw.le_iff] at h₁ h₁' ⊢
  omega

theorem Slice.Pos.le_ofSlice_iff {s : Slice} {p₀ p₁ : s.Pos} {h} {p : (s.slice p₀ p₁ h).Pos} {q : s.Pos} :
    q ≤ Pos.ofSlice p ↔ ∃ h₁, ∀ h₀, Slice.Pos.slice q p₀ p₁ h₀ h₁ ≤ p := by
  refine ⟨fun h => ⟨Std.le_trans h ofSlice_le, fun h' => ?_⟩, fun ⟨h₁, h⟩ => ?_⟩
  · simp only [← Slice.Pos.slice_ofSlice (pos := p), slice_le_slice_iff]
    simpa
  · by_cases h₀ : p₀ ≤ q
    · simpa only [← Slice.Pos.ofSlice_slice (h₁ := h₀) (h₂ := h₁), ofSlice_le_ofSlice_iff] using h h₀
    · exact Std.le_of_lt (Std.lt_of_lt_of_le (Std.not_le.1 h₀) le_ofSlice)

theorem Slice.Pos.ofSlice_lt_iff {s : Slice} {p₀ p₁ : s.Pos} {h} {p : (s.slice p₀ p₁ h).Pos} {q : s.Pos} :
    Pos.ofSlice p < q ↔ ∀ h₁, ∃ h₀, p < Slice.Pos.slice q p₀ p₁ h₀ h₁ := by
  simp [← Std.not_le, le_ofSlice_iff]

theorem Slice.Pos.lt_ofSlice_iff {s : Slice} {p₀ p₁ : s.Pos} {h} {p : (s.slice p₀ p₁ h).Pos} {q : s.Pos} :
    q < Pos.ofSlice p ↔ ∃ h₁, ∀ h₀, Slice.Pos.slice q p₀ p₁ h₀ h₁ < p := by
  refine ⟨fun h => ⟨Std.le_of_lt (Std.lt_of_lt_of_le h ofSlice_le), fun h' => ?_⟩, fun ⟨h₁, h⟩ => ?_⟩
  · simp only [← Slice.Pos.slice_ofSlice (pos := p), slice_lt_slice_iff]
    simpa
  · by_cases h₀ : p₀ ≤ q
    · simpa only [← Slice.Pos.ofSlice_slice (h₁ := h₀) (h₂ := h₁), ofSlice_lt_ofSlice_iff] using h h₀
    · exact Std.lt_of_lt_of_le (Std.not_le.1 h₀) le_ofSlice

theorem Slice.Pos.ofSlice_le_iff {s : Slice} {p₀ p₁ : s.Pos} {h} {p : (s.slice p₀ p₁ h).Pos} {q : s.Pos} :
    Pos.ofSlice p ≤ q ↔ ∀ h₁, ∃ h₀, p ≤ Slice.Pos.slice q p₀ p₁ h₀ h₁ := by
  simp [← Std.not_lt, lt_ofSlice_iff]

theorem Pos.le_ofSlice_iff {s : String} {p₀ p₁ : s.Pos} {h} {p : (s.slice p₀ p₁ h).Pos} {q : s.Pos} :
    q ≤ Pos.ofSlice p ↔ ∃ h₁, ∀ h₀, Pos.slice q p₀ p₁ h₀ h₁ ≤ p := by
  refine ⟨fun h => ⟨Std.le_trans h ofSlice_le, fun h' => ?_⟩, fun ⟨h₁, h⟩ => ?_⟩
  · simp only [← Pos.slice_ofSlice (pos := p), slice_le_slice_iff]
    simpa
  · by_cases h₀ : p₀ ≤ q
    · simpa only [← Pos.ofSlice_slice (h₁ := h₀) (h₂ := h₁), ofSlice_le_ofSlice_iff] using h h₀
    · exact Std.le_of_lt (Std.lt_of_lt_of_le (Std.not_le.1 h₀) le_ofSlice)

theorem Pos.ofSlice_lt_iff {s : String} {p₀ p₁ : s.Pos} {h} {p : (s.slice p₀ p₁ h).Pos} {q : s.Pos} :
    Pos.ofSlice p < q ↔ ∀ h₁, ∃ h₀, p < Pos.slice q p₀ p₁ h₀ h₁ := by
  simp [← Std.not_le, le_ofSlice_iff]

theorem Pos.lt_ofSlice_iff {s : String} {p₀ p₁ : s.Pos} {h} {p : (s.slice p₀ p₁ h).Pos} {q : s.Pos} :
    q < Pos.ofSlice p ↔ ∃ h₁, ∀ h₀, Pos.slice q p₀ p₁ h₀ h₁ < p := by
  refine ⟨fun h => ⟨Std.le_of_lt (Std.lt_of_lt_of_le h ofSlice_le), fun h' => ?_⟩, fun ⟨h₁, h⟩ => ?_⟩
  · simp only [← Pos.slice_ofSlice (pos := p), slice_lt_slice_iff]
    simpa
  · by_cases h₀ : p₀ ≤ q
    · simpa only [← Pos.ofSlice_slice (h₁ := h₀) (h₂ := h₁), ofSlice_lt_ofSlice_iff] using h h₀
    · exact Std.lt_of_lt_of_le (Std.not_le.1 h₀) le_ofSlice

theorem Pos.ofSlice_le_iff {s : String} {p₀ p₁ : s.Pos} {h} {p : (s.slice p₀ p₁ h).Pos} {q : s.Pos} :
    Pos.ofSlice p ≤ q ↔ ∀ h₁, ∃ h₀, p ≤ Pos.slice q p₀ p₁ h₀ h₁ := by
  simp [← Std.not_lt, lt_ofSlice_iff]

theorem Slice.Pos.slice_le_iff {s : Slice} {p₀ p₁ : s.Pos} {h} {p : (s.slice p₀ p₁ h).Pos} {q : s.Pos} {h₀ h₁} :
    Slice.Pos.slice q p₀ p₁ h₀ h₁ ≤ p ↔ q ≤ Pos.ofSlice p := by
  simp [le_ofSlice_iff, h₀, h₁]

theorem Slice.Pos.lt_slice_iff {s : Slice} {p₀ p₁ : s.Pos} {h} {p : (s.slice p₀ p₁ h).Pos} {q : s.Pos} {h₀ h₁} :
    p < Slice.Pos.slice q p₀ p₁ h₀ h₁ ↔ Pos.ofSlice p < q := by
  simp [ofSlice_lt_iff, h₀, h₁]

theorem Slice.Pos.slice_lt_iff {s : Slice} {p₀ p₁ : s.Pos} {h} {p : (s.slice p₀ p₁ h).Pos} {q : s.Pos} {h₀ h₁} :
    Slice.Pos.slice q p₀ p₁ h₀ h₁ < p ↔ q < Pos.ofSlice p := by
  simp [lt_ofSlice_iff, h₀, h₁]

theorem Slice.Pos.le_slice_iff {s : Slice} {p₀ p₁ : s.Pos} {h} {p : (s.slice p₀ p₁ h).Pos} {q : s.Pos} {h₀ h₁} :
    p ≤ Slice.Pos.slice q p₀ p₁ h₀ h₁ ↔ Pos.ofSlice p ≤ q := by
  simp [ofSlice_le_iff, h₀, h₁]

theorem Pos.slice_le_iff {s : String} {p₀ p₁ : s.Pos} {h} {p : (s.slice p₀ p₁ h).Pos} {q : s.Pos} {h₀ h₁} :
    Pos.slice q p₀ p₁ h₀ h₁ ≤ p ↔ q ≤ Pos.ofSlice p := by
  simp [le_ofSlice_iff, h₀, h₁]

theorem Pos.lt_slice_iff {s : String} {p₀ p₁ : s.Pos} {h} {p : (s.slice p₀ p₁ h).Pos} {q : s.Pos} {h₀ h₁} :
    p < Pos.slice q p₀ p₁ h₀ h₁ ↔ Pos.ofSlice p < q := by
  simp [ofSlice_lt_iff, h₀, h₁]

theorem Pos.slice_lt_iff {s : String} {p₀ p₁ : s.Pos} {h} {p : (s.slice p₀ p₁ h).Pos} {q : s.Pos} {h₀ h₁} :
    Pos.slice q p₀ p₁ h₀ h₁ < p ↔ q < Pos.ofSlice p := by
  simp [lt_ofSlice_iff, h₀, h₁]

theorem Pos.le_slice_iff {s : String} {p₀ p₁ : s.Pos} {h} {p : (s.slice p₀ p₁ h).Pos} {q : s.Pos} {h₀ h₁} :
    p ≤ Pos.slice q p₀ p₁ h₀ h₁ ↔ Pos.ofSlice p ≤ q := by
  simp [ofSlice_le_iff, h₀, h₁]

theorem Slice.Pos.ofSlice_ne_endPos {s : Slice} {p₀ p₁ : s.Pos} {h} {p : (s.slice p₀ p₁ h).Pos}
    (h : p ≠ (s.slice p₀ p₁ h).endPos) : Pos.ofSlice p ≠ s.endPos := by
  refine (lt_endPos_iff _).1 (Std.lt_of_lt_of_le ?_ (le_endPos p₁))
  simpa [← lt_endPos_iff, ← ofSlice_lt_ofSlice_iff] using h

theorem Slice.Pos.ne_endPos_of_slice_ne_endPos {s : Slice} {p p₀ p₁ : s.Pos} {h₁ h₂}
    (h : Pos.slice p p₀ p₁ h₁ h₂ ≠ Slice.endPos _) : p ≠ s.endPos := by
  rw [← Pos.ofSlice_slice (h₁ := h₁) (h₂ := h₂)]
  apply Pos.ofSlice_ne_endPos h

theorem Slice.Pos.ofSlice_ne_startPos {s : Slice} {p₀ p₁ : s.Pos} {h} {p : (s.slice p₀ p₁ h).Pos}
    (h : p ≠ (s.slice p₀ p₁ h).startPos) : Pos.ofSlice p ≠ s.startPos := by
  refine (startPos_lt_iff _).1 (Std.lt_of_le_of_lt (startPos_le p₀) ?_)
  simpa [← startPos_lt_iff, ← ofSlice_lt_ofSlice_iff] using h

theorem Slice.Pos.ne_startPos_of_slice_ne_startPos {s : Slice} {p p₀ p₁ : s.Pos} {h₁ h₂}
    (h : Pos.slice p p₀ p₁ h₁ h₂ ≠ Slice.startPos _) : p ≠ s.startPos := by
  rw [← Pos.ofSlice_slice (h₁ := h₁) (h₂ := h₂)]
  apply Pos.ofSlice_ne_startPos h

theorem Pos.ofSlice_ne_endPos {s : String} {p₀ p₁ : s.Pos} {h} {p : (s.slice p₀ p₁ h).Pos}
    (h : p ≠ (s.slice p₀ p₁ h).endPos) : Pos.ofSlice p ≠ s.endPos := by
  refine (lt_endPos_iff _).1 (Std.lt_of_lt_of_le ?_ (le_endPos p₁))
  simpa [← Slice.Pos.lt_endPos_iff, ← ofSlice_lt_ofSlice_iff] using h

theorem Pos.ne_endPos_of_slice_ne_endPos {s : String} {p p₀ p₁ : s.Pos} {h₁ h₂}
    (h : Pos.slice p p₀ p₁ h₁ h₂ ≠ Slice.endPos _) : p ≠ s.endPos := by
  rw [← Pos.ofSlice_slice (h₁ := h₁) (h₂ := h₂)]
  apply Pos.ofSlice_ne_endPos h

theorem Pos.ofSlice_ne_startPos {s : String} {p₀ p₁ : s.Pos} {h} {p : (s.slice p₀ p₁ h).Pos}
    (h : p ≠ (s.slice p₀ p₁ h).startPos) : Pos.ofSlice p ≠ s.startPos := by
  refine (startPos_lt_iff _).1 (Std.lt_of_le_of_lt (startPos_le p₀) ?_)
  simpa [← Slice.Pos.startPos_lt_iff, ← ofSlice_lt_ofSlice_iff] using h

theorem Pos.ne_startPos_of_slice_ne_startPos {s : String} {p p₀ p₁ : s.Pos} {h₁ h₂}
    (h : Pos.slice p p₀ p₁ h₁ h₂ ≠ Slice.startPos _) : p ≠ s.startPos := by
  rw [← Pos.ofSlice_slice (h₁ := h₁) (h₂ := h₂)]
  apply Pos.ofSlice_ne_startPos h

@[simp]
theorem Slice.Pos.offset_le_rawEndPos {s : Slice} {p : s.Pos} :
    p.offset ≤ s.rawEndPos :=
  p.isValidForSlice.le_rawEndPos

@[simp]
theorem Pos.offset_le_rawEndPos {s : String} {p : s.Pos} :
    p.offset ≤ s.rawEndPos :=
  p.isValid.le_rawEndPos

@[simp]
theorem Slice.Pos.byteIdx_offset_le_utf8ByteSize {s : Slice} {p : s.Pos} :
    p.offset.byteIdx ≤ s.utf8ByteSize := by
  simp [← byteIdx_rawEndPos, ← Pos.Raw.le_iff]

@[simp]
theorem Pos.byteIdx_offset_le_utf8ByteSize {s : String} {p : s.Pos} :
    p.offset.byteIdx ≤ s.utf8ByteSize := by
  simp [← byteIdx_rawEndPos, ← Pos.Raw.le_iff]

@[simp]
theorem Slice.Pos.offset_lt_rawEndPos_iff {s : Slice} {p : s.Pos} :
    p.offset < s.rawEndPos ↔ p ≠ s.endPos := by
  simp [Std.lt_iff_le_and_ne, p.offset_le_rawEndPos, Pos.ext_iff]

@[simp]
theorem Pos.offset_lt_rawEndPos_iff {s : String} {p : s.Pos} :
    p.offset < s.rawEndPos ↔ p ≠ s.endPos := by
  simp [Std.lt_iff_le_and_ne, p.offset_le_rawEndPos, Pos.ext_iff]

@[simp]
theorem Slice.Pos.getUTF8Byte_offset {s : Slice} {p : s.Pos} {h} :
    s.getUTF8Byte p.offset h = p.byte (by simpa using h) := by
  simp [Pos.byte]

theorem Slice.Pos.isUTF8FirstByte_getUTF8Byte_offset {s : Slice} {p : s.Pos} {h} :
    (s.getUTF8Byte p.offset h).IsUTF8FirstByte := by
  simpa [getUTF8Byte_offset] using isUTF8FirstByte_byte

theorem Pos.getUTF8Byte_offset {s : String} {p : s.Pos} {h} :
    s.getUTF8Byte p.offset h = p.byte (by simpa using h) := by
  simp only [getUTF8Byte_eq_getUTF8Byte_toSlice, ← Pos.offset_toSlice,
    Slice.Pos.getUTF8Byte_offset, byte_toSlice]

theorem Pos.isUTF8FirstByte_getUTF8Byte_offset {s : String} {p : s.Pos} {h} :
    (s.getUTF8Byte p.offset h).IsUTF8FirstByte := by
  simpa [getUTF8Byte_offset] using isUTF8FirstByte_byte

theorem Slice.Pos.get_eq_get_ofSliceTo {s : Slice} {p₀ : s.Pos} {pos : (s.sliceTo p₀).Pos} {h} :
    pos.get h = (ofSliceTo pos).get (ofSliceTo_ne_endPos h) := by
  simp [Slice.Pos.get]

theorem Slice.Pos.get_sliceTo {s : Slice} {p₀ p : s.Pos} {h h'} :
    (Pos.sliceTo p₀ p h).get h' = p.get (ne_endPos_of_sliceTo_ne_endPos h') := by
  simp [get_eq_get_ofSliceTo]

theorem Pos.get_eq_get_ofSliceTo {s : String} {p₀ : s.Pos}
    {pos : (s.sliceTo p₀).Pos} {h} :
    pos.get h = (ofSliceTo pos).get (ofSliceTo_ne_endPos h) := by
  simp [Pos.get, Slice.Pos.get]

theorem Pos.get_sliceTo {s : String} {p₀ p : s.Pos} {h h'} :
    (Pos.sliceTo p₀ p h).get h' = p.get (ne_endPos_of_sliceTo_ne_endPos h') := by
  simp [get_eq_get_ofSliceTo]

theorem Slice.Pos.get_eq_get_ofSlice {s : Slice} {p₀ p₁ : s.Pos} {h}
    {pos : (s.slice p₀ p₁ h).Pos} {h'} :
    pos.get h' = (ofSlice pos).get (ofSlice_ne_endPos h') := by
  simp [Slice.Pos.get, Nat.add_assoc]

theorem Slice.Pos.get_slice {s : Slice} {p p₀ p₁ : s.Pos} {h₁ h₂ h} :
    (Pos.slice p p₀ p₁ h₁ h₂).get h = p.get (ne_endPos_of_slice_ne_endPos h) := by
  simp [get_eq_get_ofSlice]

theorem Pos.get_eq_get_ofSlice {s : String} {p₀ p₁ : s.Pos} {h}
    {pos : (s.slice p₀ p₁ h).Pos} {h'} :
    pos.get h' = (ofSlice pos).get (ofSlice_ne_endPos h') := by
  simp [Pos.get, Slice.Pos.get]

theorem Pos.get_slice {s : String} {p p₀ p₁ : s.Pos} {h₁ h₂ h} :
    (Pos.slice p p₀ p₁ h₁ h₂).get h = p.get (ne_endPos_of_slice_ne_endPos h) := by
  simp [get_eq_get_ofSlice]

theorem Slice.Pos.ofSlice_next {s : Slice} {p₀ p₁ : s.Pos} {h}
    {p : (s.slice p₀ p₁ h).Pos} {h'} :
    Pos.ofSlice (p.next h') = (Pos.ofSlice p).next (ofSlice_ne_endPos h') := by
  simp only [Slice.Pos.ext_iff, Pos.Raw.ext_iff, Slice.Pos.offset_next, Slice.Pos.offset_ofSlice]
  rw [Slice.Pos.get_eq_get_ofSlice (h' := h')]
  simp [Pos.Raw.offsetBy, Nat.add_assoc]

theorem Pos.ofSlice_next {s : String} {p₀ p₁ : s.Pos} {h}
    {p : (s.slice p₀ p₁ h).Pos} {h'} :
    Pos.ofSlice (p.next h') = (Pos.ofSlice p).next (ofSlice_ne_endPos h') := by
  simp only [Pos.ext_iff, Pos.Raw.ext_iff, Slice.Pos.offset_next, Pos.offset_next,
    Pos.offset_ofSlice]
  rw [Pos.get_eq_get_ofSlice (h' := h')]
  simp [Pos.Raw.offsetBy, Nat.add_assoc]

end String
