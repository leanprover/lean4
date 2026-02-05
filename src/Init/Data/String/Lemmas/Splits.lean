/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Markus Himmel
-/
module

prelude
public import Init.Data.String.Basic
import Init.Data.ByteArray.Lemmas
import Init.Data.String.Lemmas.Basic
import Init.Data.Nat.MinMax

/-!
# `Splits` predicates on `String.Pos` and `String.Slice.Pos`.

We introduce the predicate `p.Splits t₁ t₂` for a position `p` on a string or slice `s`, which means
that `s = t₁ ++ t₂` with `p` lying between the two parts. This is a useful primitive when verifying
string operations.
-/

public section

namespace String

/--
We say that `p` splits `s` into `t₁` and `t₂` if `s = t₁ ++ t₂` and `p` is the position between `t₁`
and `t₂`.
-/
structure Pos.Splits {s : String} (p : s.Pos) (t₁ t₂ : String) : Prop where
  eq_append : s = t₁ ++ t₂
  offset_eq_rawEndPos : p.offset = t₁.rawEndPos

/--
We say that `p` splits `s` into `t₁` and `t₂` if `s = t₁ ++ t₂` and `p` is the position between `t₁`
and `t₂`.
-/
structure Slice.Pos.Splits {s : Slice} (p : s.Pos) (t₁ t₂ : String) : Prop where
  eq_append : s.copy = t₁ ++ t₂
  offset_eq_rawEndPos : p.offset = t₁.rawEndPos

@[simp]
theorem Pos.splits_cast_iff {s₁ s₂ : String} {h : s₁ = s₂} {p : s₁.Pos} {t₁ t₂ : String} :
    (p.cast h).Splits t₁ t₂ ↔ p.Splits t₁ t₂ := by
  subst h; simp

theorem Pos.Splits.cast {s₁ s₂ : String} {p : s₁.Pos} {t₁ t₂ : String} (h : s₁ = s₂) :
    p.Splits t₁ t₂ → (p.cast h).Splits t₁ t₂ :=
  splits_cast_iff.mpr

@[simp]
theorem Slice.Pos.splits_cast_iff {s₁ s₂ : Slice} {h : s₁ = s₂} {p : s₁.Pos} {t₁ t₂ : String} :
    (p.cast h).Splits t₁ t₂ ↔ p.Splits t₁ t₂ := by
  subst h; simp

theorem Slice.Pos.Splits.cast {s₁ s₂ : Slice} {p : s₁.Pos} {t₁ t₂ : String} (h : s₁ = s₂) :
    p.Splits t₁ t₂ → (p.cast h).Splits t₁ t₂ :=
  splits_cast_iff.mpr

theorem Slice.Pos.Splits.copy {s : Slice} {p : s.Pos} {t₁ t₂ : String}
    (h : p.Splits t₁ t₂) : p.copy.Splits t₁ t₂ where
  eq_append := h.eq_append
  offset_eq_rawEndPos := by simpa using h.offset_eq_rawEndPos

theorem Slice.Pos.splits_of_splits_copy {s : Slice} {p : s.Pos} {t₁ t₂ : String}
    (h : p.copy.Splits t₁ t₂) : p.Splits t₁ t₂ where
  eq_append := h.eq_append
  offset_eq_rawEndPos := by simpa using h.offset_eq_rawEndPos

@[simp]
theorem Slice.Pos.splits_copy_iff {s : Slice} {p : s.Pos} {t₁ t₂ : String} :
    p.copy.Splits t₁ t₂ ↔ p.Splits t₁ t₂ :=
  ⟨splits_of_splits_copy, (·.copy)⟩

@[simp]
theorem Pos.splits_toSlice_iff {s : String} {p : s.Pos} {t₁ t₂ : String} :
    p.toSlice.Splits t₁ t₂ ↔ p.Splits t₁ t₂ := by
  rw [← Slice.Pos.splits_copy_iff, p.copy_toSlice_eq_cast, splits_cast_iff]

theorem Pos.Splits.toSlice {s : String} {p : s.Pos} {t₁ t₂ : String}
    (h : p.Splits t₁ t₂) : p.toSlice.Splits t₁ t₂ :=
  splits_toSlice_iff.mpr h

theorem Pos.splits {s : String} (p : s.Pos) :
    p.Splits (s.sliceTo p).copy (s.sliceFrom p).copy where
  eq_append := by simp [← toByteArray_inj, Slice.toByteArray_copy, ← size_toByteArray]
  offset_eq_rawEndPos := by simp

theorem Slice.Pos.splits {s : Slice} (p : s.Pos) :
    p.Splits (s.sliceTo p).copy (s.sliceFrom p).copy where
  eq_append := copy_eq_copy_sliceTo
  offset_eq_rawEndPos := by simp

theorem Pos.Splits.toByteArray_left_eq {s : String} {p : s.Pos} {t₁ t₂}
    (h : p.Splits t₁ t₂) : t₁.toByteArray = s.toByteArray.extract 0 p.offset.byteIdx := by
  simp [h.eq_append, h.offset_eq_rawEndPos, ByteArray.extract_append_eq_left]

theorem Pos.Splits.toByteArray_right_eq {s : String} {p : s.Pos} {t₁ t₂}
    (h : p.Splits t₁ t₂) : t₂.toByteArray = s.toByteArray.extract p.offset.byteIdx s.utf8ByteSize := by
  simp [h.eq_append, h.offset_eq_rawEndPos, ByteArray.extract_append_eq_right]

theorem Pos.Splits.eq_left {s : String} {p : s.Pos} {t₁ t₂ t₃ t₄}
    (h₁ : p.Splits t₁ t₂) (h₂ : p.Splits t₃ t₄) : t₁ = t₃ := by
  rw [← String.toByteArray_inj, h₁.toByteArray_left_eq, h₂.toByteArray_left_eq]

theorem Pos.Splits.eq_right {s : String} {p : s.Pos} {t₁ t₂ t₃ t₄}
    (h₁ : p.Splits t₁ t₂) (h₂ : p.Splits t₃ t₄) : t₂ = t₄ := by
  rw [← String.toByteArray_inj, h₁.toByteArray_right_eq, h₂.toByteArray_right_eq]

theorem Pos.Splits.eq {s : String} {p : s.Pos} {t₁ t₂ t₃ t₄}
    (h₁ : p.Splits t₁ t₂) (h₂ : p.Splits t₃ t₄) : t₁ = t₃ ∧ t₂ = t₄ :=
  ⟨h₁.eq_left h₂, h₁.eq_right h₂⟩

theorem Slice.Pos.Splits.eq_left {s : Slice} {p : s.Pos} {t₁ t₂ t₃ t₄}
    (h₁ : p.Splits t₁ t₂) (h₂ : p.Splits t₃ t₄) : t₁ = t₃ :=
  (splits_copy_iff.2 h₁).eq_left (splits_copy_iff.2 h₂)

theorem Slice.Pos.Splits.eq_right {s : Slice} {p : s.Pos} {t₁ t₂ t₃ t₄}
    (h₁ : p.Splits t₁ t₂) (h₂ : p.Splits t₃ t₄) : t₂ = t₄ :=
  (splits_copy_iff.2 h₁).eq_right (splits_copy_iff.2 h₂)

theorem Slice.Pos.Splits.eq {s : Slice} {p : s.Pos} {t₁ t₂ t₃ t₄}
    (h₁ : p.Splits t₁ t₂) (h₂ : p.Splits t₃ t₄) : t₁ = t₃ ∧ t₂ = t₄ :=
  (splits_copy_iff.2 h₁).eq (splits_copy_iff.2 h₂)

@[simp]
theorem splits_endPos (s : String) : s.endPos.Splits s "" where
  eq_append := by simp
  offset_eq_rawEndPos := by simp

@[simp]
theorem splits_endPos_iff {s : String} :
    s.endPos.Splits t₁ t₂ ↔ t₁ = s ∧ t₂ = "" :=
  ⟨fun h => ⟨h.eq_left s.splits_endPos, h.eq_right s.splits_endPos⟩,
   by rintro ⟨rfl, rfl⟩; exact t₁.splits_endPos⟩

theorem Pos.Splits.eq_endPos_iff {s : String} {p : s.Pos} (h : p.Splits t₁ t₂) :
    p = s.endPos ↔ t₂ = "" :=
  ⟨fun h' => h.eq_right (h' ▸ s.splits_endPos),
   by rintro rfl; simp [Pos.ext_iff, h.offset_eq_rawEndPos, h.eq_append]⟩

theorem splits_startPos (s : String) : s.startPos.Splits "" s where
  eq_append := by simp
  offset_eq_rawEndPos := by simp

@[simp]
theorem splits_startPos_iff {s : String} :
    s.startPos.Splits t₁ t₂ ↔ t₁ = "" ∧ t₂ = s :=
  ⟨fun h => ⟨h.eq_left s.splits_startPos, h.eq_right s.splits_startPos⟩,
   by rintro ⟨rfl, rfl⟩; exact t₂.splits_startPos⟩

theorem Pos.Splits.eq_startPos_iff {s : String} {p : s.Pos} (h : p.Splits t₁ t₂) :
    p = s.startPos ↔ t₁ = "" :=
  ⟨fun h' => h.eq_left (h' ▸ s.splits_startPos),
   by rintro rfl; simp [Pos.ext_iff, h.offset_eq_rawEndPos]⟩

@[simp]
theorem Slice.splits_endPos (s : Slice) : s.endPos.Splits s.copy "" where
  eq_append := by simp
  offset_eq_rawEndPos := by simp

@[simp]
theorem Slice.splits_endPos_iff {s : Slice} :
    s.endPos.Splits t₁ t₂ ↔ t₁ = s.copy ∧ t₂ = "" := by
  rw [← Pos.splits_copy_iff, ← endPos_copy, String.splits_endPos_iff]

theorem Slice.Pos.Splits.eq_endPos_iff {s : Slice} {p : s.Pos} (h : p.Splits t₁ t₂) :
    p = s.endPos ↔ t₂ = "" := by
  rw [← copy_inj, ← endPos_copy, h.copy.eq_endPos_iff]

@[simp]
theorem Slice.splits_startPos (s : Slice) : s.startPos.Splits "" s.copy where
  eq_append := by simp
  offset_eq_rawEndPos := by simp

@[simp]
theorem Slice.splits_startPos_iff {s : Slice} :
    s.startPos.Splits t₁ t₂ ↔ t₁ = "" ∧ t₂ = s.copy := by
  rw [← Pos.splits_copy_iff, ← startPos_copy, String.splits_startPos_iff]

theorem Slice.Pos.Splits.eq_startPos_iff {s : Slice} {p : s.Pos} (h : p.Splits t₁ t₂) :
    p = s.startPos ↔ t₁ = "" := by
  rw [← copy_inj, ← startPos_copy, h.copy.eq_startPos_iff]

theorem Pos.splits_next_right {s : String} (p : s.Pos) (hp : p ≠ s.endPos) :
    p.Splits (s.sliceTo p).copy (singleton (p.get hp) ++ (s.sliceFrom (p.next hp)).copy) where
  eq_append := by simpa [← append_assoc] using p.eq_copy_sliceTo_append_get hp
  offset_eq_rawEndPos := by simp

theorem Pos.splits_next {s : String} (p : s.Pos) (hp : p ≠ s.endPos) :
    (p.next hp).Splits ((s.sliceTo p).copy ++ singleton (p.get hp)) (s.sliceFrom (p.next hp)).copy where
  eq_append := p.eq_copy_sliceTo_append_get hp
  offset_eq_rawEndPos := by simp

theorem Slice.Pos.splits_next_right {s : Slice} (p : s.Pos) (hp : p ≠ s.endPos) :
    p.Splits (s.sliceTo p).copy (singleton (p.get hp) ++ (s.sliceFrom (p.next hp)).copy) where
  eq_append := by simpa [← append_assoc] using p.copy_eq_copy_sliceTo_append_get hp
  offset_eq_rawEndPos := by simp

theorem Slice.Pos.splits_next {s : Slice} (p : s.Pos) (hp : p ≠ s.endPos) :
    (p.next hp).Splits ((s.sliceTo p).copy ++ singleton (p.get hp)) (s.sliceFrom (p.next hp)).copy where
  eq_append := p.copy_eq_copy_sliceTo_append_get hp
  offset_eq_rawEndPos := by simp

theorem Pos.Splits.exists_eq_singleton_append {s : String} {p : s.Pos}
    (hp : p ≠ s.endPos) (h : p.Splits t₁ t₂) : ∃ t₂', t₂ = singleton (p.get hp) ++ t₂' :=
  ⟨(s.sliceFrom (p.next hp)).copy, h.eq_right (p.splits_next_right hp)⟩

theorem Pos.Splits.exists_eq_append_singleton {s : String} {p : s.Pos}
    (hp : p ≠ s.endPos) (h : (p.next hp).Splits t₁ t₂) : ∃ t₁', t₁ = t₁' ++ singleton (p.get hp) :=
  ⟨(s.sliceTo p).copy, h.eq_left (p.splits_next hp)⟩

theorem Slice.Pos.Splits.exists_eq_singleton_append {s : Slice} {p : s.Pos}
    (hp : p ≠ s.endPos) (h : p.Splits t₁ t₂) : ∃ t₂', t₂ = singleton (p.get hp) ++ t₂' :=
  ⟨(s.sliceFrom (p.next hp)).copy, h.eq_right (p.splits_next_right hp)⟩

theorem Slice.Pos.Splits.exists_eq_append_singleton {s : Slice} {p : s.Pos}
    (hp : p ≠ s.endPos) (h : (p.next hp).Splits t₁ t₂) : ∃ t₁', t₁ = t₁' ++ singleton (p.get hp) :=
  ⟨(s.sliceTo p).copy, h.eq_left (p.splits_next hp)⟩

theorem Pos.Splits.ne_endPos_of_singleton {s : String} {p : s.Pos}
    (h : p.Splits t₁ (singleton c ++ t₂)) : p ≠ s.endPos := by
  simp [h.eq_endPos_iff]

theorem Pos.Splits.ne_startPos_of_singleton {s : String} {p : s.Pos}
    (h : p.Splits (t₁ ++ singleton c) t₂) : p ≠ s.startPos := by
  simp [h.eq_startPos_iff]

theorem Slice.Pos.Splits.ne_endPos_of_singleton {s : Slice} {p : s.Pos}
    (h : p.Splits t₁ (singleton c ++ t₂)) : p ≠ s.endPos := by
  simp [h.eq_endPos_iff]

theorem Slice.Pos.Splits.ne_startPos_of_singleton {s : Slice} {p : s.Pos}
    (h : p.Splits (t₁ ++ singleton c) t₂) : p ≠ s.startPos := by
  simp [h.eq_startPos_iff]

/-- You might want to invoke `Pos.Splits.exists_eq_singleton_append` to be able to apply this. -/
theorem Pos.Splits.next {s : String} {p : s.Pos}
    (h : p.Splits t₁ (singleton c ++ t₂)) : (p.next h.ne_endPos_of_singleton).Splits (t₁ ++ singleton c) t₂ := by
  generalize h.ne_endPos_of_singleton = hp
  obtain ⟨rfl, rfl, rfl⟩ := by simpa using h.eq (splits_next_right p hp)
  exact splits_next p hp

/-- You might want to invoke `Slice.Pos.Splits.exists_eq_singleton_append` to be able to apply this. -/
theorem Slice.Pos.Splits.next {s : Slice} {p : s.Pos}
    (h : p.Splits t₁ (singleton c ++ t₂)) : (p.next h.ne_endPos_of_singleton).Splits (t₁ ++ singleton c) t₂ := by
  generalize h.ne_endPos_of_singleton = hp
  obtain ⟨rfl, rfl, rfl⟩ := by simpa using h.eq (splits_next_right p hp)
  exact splits_next p hp

end String
