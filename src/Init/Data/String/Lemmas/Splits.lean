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
import Init.Data.String.Lemmas.IsEmpty
import Init.Data.String.Lemmas.Order
import Init.Data.String.OrderInstances
import Init.Data.Nat.Order
import Init.Omega

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

theorem Pos.Splits.of_eq {s : String} {p : s.Pos} {t₁ t₂ t₃ t₄}
    (h : p.Splits t₁ t₂) (h₁ : t₁ = t₃) (h₂ : t₂ = t₄) : p.Splits t₃ t₄ :=
  h₁ ▸ h₂ ▸ h

theorem Slice.Pos.Splits.of_eq {s : Slice} {p : s.Pos} {t₁ t₂ t₃ t₄}
    (h : p.Splits t₁ t₂) (h₁ : t₁ = t₃) (h₂ : t₂ = t₄) : p.Splits t₃ t₄ :=
  h₁ ▸ h₂ ▸ h

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

theorem Slice.sliceTo_copy_eq_iff_exists_splits {s : Slice} {p : s.Pos} {t₁ : String} :
    (s.sliceTo p).copy = t₁ ↔ ∃ t₂, p.Splits t₁ t₂ := by
  refine ⟨?_, ?_⟩
  · rintro rfl
    exact ⟨_, p.splits⟩
  · rintro ⟨t₂, h⟩
    exact p.splits.eq_left h

theorem sliceTo_copy_eq_iff_exists_splits {s : String} {p : s.Pos} {t₁ : String} :
    (s.sliceTo p).copy = t₁ ↔ ∃ t₂, p.Splits t₁ t₂ := by
  refine ⟨?_, ?_⟩
  · rintro rfl
    exact ⟨_, p.splits⟩
  · rintro ⟨t₂, h⟩
    exact p.splits.eq_left h

theorem Slice.Pos.Splits.pos_eq {s : Slice} {p q : s.Pos} {s t : String} (h : p.Splits s t)
    (h' : q.Splits s t) : p = q := by
  rw [Slice.Pos.ext_iff, h.offset_eq_rawEndPos, h'.offset_eq_rawEndPos]

theorem Pos.Splits.pos_eq {s : String} {p q : s.Pos} {s t : String} (h : p.Splits s t)
    (h' : q.Splits s t) : p = q := by
  rw [Pos.ext_iff, h.offset_eq_rawEndPos, h'.offset_eq_rawEndPos]

theorem Slice.Pos.Splits.get_eq_of_singleton {s : Slice} {p : s.Pos} {h : p ≠ s.endPos}
    {t₁ t₂ : String} {c : Char} (hs : (p.next h).Splits (t₁ ++ singleton c) t₂) : p.get h = c := by
  have := hs.eq_left (splits_next p h)
  simp only [append_singleton, push_inj] at this
  rw [this.2]

theorem Pos.Splits.get_eq_of_singleton {s : String} {p : s.Pos} {h : p ≠ s.endPos}
    {t₁ t₂ : String} {c : Char} (hs : (p.next h).Splits (t₁ ++ singleton c) t₂) : p.get h = c := by
  have := hs.eq_left (splits_next p h)
  simp only [append_singleton, push_inj] at this
  rw [this.2]

theorem Slice.splits_singleton_iff {s : Slice} {p : s.Pos} {c : Char} {t : String} :
    p.Splits (singleton c) t ↔
      ∃ h, p = s.startPos.next h ∧ s.startPos.get h = c ∧ s.copy = singleton c ++ t := by
  refine ⟨fun h => ?_, ?_⟩
  · have : s.startPos ≠ s.endPos := by
      simp [startPos_ne_endPos_iff, ← copy_ne_empty_iff, h.eq_append]
    have spl : (s.startPos.next this).Splits (singleton c) t := by
      rw [← empty_append (s := singleton c)]
      apply Pos.Splits.next
      simp [h.eq_append]
    refine ⟨this, ⟨h.pos_eq spl, ?_, h.eq_append⟩⟩
    rw [← empty_append (s := singleton c)] at spl
    exact spl.get_eq_of_singleton
  · rintro ⟨h, ⟨rfl, rfl, h'⟩⟩
    rw [← String.empty_append (s := singleton (s.startPos.get h))]
    exact Pos.Splits.next (by simp [h'])

theorem splits_singleton_iff {s : String} {p : s.Pos} {c : Char} {t : String} :
    p.Splits (singleton c) t ↔
      ∃ h, p = s.startPos.next h ∧ s.startPos.get h = c ∧ s = singleton c ++ t := by
  rw [← Pos.splits_toSlice_iff, Slice.splits_singleton_iff]
  simp [← Pos.ofToSlice_inj]

@[simp]
theorem Slice.copy_sliceTo_startPos {s : Slice} : (s.sliceTo s.startPos).copy = "" :=
  s.startPos.splits.eq_left s.splits_startPos

@[simp]
theorem copy_sliceTo_startPos {s : String} : (s.sliceTo s.startPos).copy = "" :=
  s.startPos.splits.eq_left s.splits_startPos

theorem Slice.splits_next_startPos {s : Slice} {h : s.startPos ≠ s.endPos} :
    (s.startPos.next h).Splits
      (singleton (s.startPos.get h)) (s.sliceFrom (s.startPos.next h)).copy := by
  rw [← String.empty_append (s := singleton (s.startPos.get h))]
  apply Slice.Pos.Splits.next
  have := Slice.Pos.splits_next_right s.startPos h
  rwa [copy_sliceTo_startPos] at this

theorem splits_next_startPos {s : String} {h : s.startPos ≠ s.endPos} :
    (s.startPos.next h).Splits
      (singleton (s.startPos.get h)) (s.sliceFrom (s.startPos.next h)).copy := by
  rw [← Pos.splits_toSlice_iff]
  apply (Slice.splits_next_startPos).of_eq <;> simp [String.Pos.next_toSlice]

theorem Slice.Pos.Splits.toByteArray_eq_left {s : Slice} {p : s.Pos} {t₁ t₂ : String} (h : p.Splits t₁ t₂) :
    t₁.toByteArray = s.copy.toByteArray.extract 0 p.offset.byteIdx := by
  rw [h.eq_left p.splits]
  simp only [toByteArray_copy, str_sliceTo, startInclusive_sliceTo, endExclusive_sliceTo,
    offset_str, Pos.Raw.byteIdx_offsetBy, ByteArray.extract_extract, Nat.add_zero]
  rw [Nat.min_eq_left]
  simpa [String.Pos.le_iff, Pos.Raw.le_iff] using p.str_le_endExclusive

theorem Pos.Splits.toByteArray_eq_left {s : String} {p : s.Pos} {t₁ t₂ : String} (h : p.Splits t₁ t₂) :
    t₁.toByteArray = s.toByteArray.extract 0 p.offset.byteIdx := by
  rw [(splits_toSlice_iff.2 h).toByteArray_eq_left, copy_toSlice, Pos.offset_toSlice]

theorem Slice.Pos.Splits.toByteArray_eq_right {s : Slice} {p : s.Pos} {t₁ t₂ : String} (h : p.Splits t₁ t₂) :
    t₂.toByteArray = s.copy.toByteArray.extract p.offset.byteIdx s.copy.toByteArray.size := by
  rw [h.eq_right p.splits]
  simp only [toByteArray_copy, str_sliceFrom, startInclusive_sliceFrom, offset_str,
    Pos.Raw.byteIdx_offsetBy, endExclusive_sliceFrom, ByteArray.size_extract, size_toByteArray,
    ByteArray.extract_extract]
  rw [Nat.min_eq_right]
  rw [Nat.min_eq_left (by simp)]
  have := s.startInclusive_le_endExclusive
  rw [String.Pos.le_iff, Pos.Raw.le_iff] at this
  omega

theorem Pos.Splits.toByteArray_eq_right {s : String} {p : s.Pos} {t₁ t₂ : String} (h : p.Splits t₁ t₂) :
    t₂.toByteArray = s.toByteArray.extract p.offset.byteIdx s.toByteArray.size := by
  rw [(splits_toSlice_iff.2 h).toByteArray_eq_right, copy_toSlice, Pos.offset_toSlice]

theorem Slice.Pos.Splits.le_iff_exists_eq_append {s : Slice} {p₁ p₂ : s.Pos} {t₁ t₂ t₃ t₄ : String}
    (h : p₁.Splits t₁ t₂) (h' : p₂.Splits t₃ t₄) : p₁ ≤ p₂ ↔ ∃ t₅, t₃ = t₁ ++ t₅ ∧ t₂ = t₅ ++ t₄ := by
  refine ⟨fun hp => ?_, ?_⟩
  · refine ⟨(s.slice p₁ p₂ hp).copy, ?_, ?_⟩
    · simp only [← toByteArray_inj, toByteArray_append, h'.toByteArray_eq_left,
        h.toByteArray_eq_left, toByteArray_copy_slice]
      rw [← ByteArray.extract_eq_extract_append_extract _ (by simp) hp]
    · simp [← toByteArray_inj, h.toByteArray_eq_right, h'.toByteArray_eq_right,
        toByteArray_copy_slice, ← ByteArray.extract_eq_extract_append_extract _ hp]
  · rintro ⟨t₅, rfl, rfl⟩
    simp [Pos.Raw.le_iff, Slice.Pos.le_iff, h.offset_eq_rawEndPos, h'.offset_eq_rawEndPos]

theorem Slice.Pos.Splits.lt_iff_exists_eq_append {s : Slice} {p₁ p₂ : s.Pos} {t₁ t₂ t₃ t₄ : String}
    (h : p₁.Splits t₁ t₂) (h' : p₂.Splits t₃ t₄) :
    p₁ < p₂ ↔ ∃ t₅, t₅ ≠ "" ∧ t₃ = t₁ ++ t₅ ∧ t₂ = t₅ ++ t₄ := by
  rw [Std.lt_iff_le_and_ne, h.le_iff_exists_eq_append h']
  refine ⟨?_, ?_⟩
  · rintro ⟨⟨t₅, ⟨rfl, rfl⟩⟩, h₂⟩
    refine ⟨t₅, fun hx => ?_, rfl, rfl⟩
    simp [hx] at h h'
    exact h₂ (h.pos_eq h')
  · rintro ⟨t₅, ⟨ht₅, rfl, rfl⟩⟩
    refine ⟨⟨t₅, rfl, rfl⟩, fun hx => ht₅ ?_⟩
    have := h.eq_left (hx ▸ h')
    simpa [eq_comm (a := t₁)] using (h.eq_left (hx ▸ h') :)

theorem Pos.Splits.le_iff_exists_eq_append {s : String} {p₁ p₂ : s.Pos} {t₁ t₂ t₃ t₄ : String}
    (h : p₁.Splits t₁ t₂) (h' : p₂.Splits t₃ t₄) : p₁ ≤ p₂ ↔ ∃ t₅, t₃ = t₁ ++ t₅ ∧ t₂ = t₅ ++ t₄ := by
  rw [← toSlice_le, (splits_toSlice_iff.2 h).le_iff_exists_eq_append (splits_toSlice_iff.2 h')]

theorem Pos.Splits.lt_iff_exists_eq_append {s : String} {p₁ p₂ : s.Pos} {t₁ t₂ t₃ t₄ : String}
    (h : p₁.Splits t₁ t₂) (h' : p₂.Splits t₃ t₄) :
    p₁ < p₂ ↔ ∃ t₅, t₅ ≠ "" ∧ t₃ = t₁ ++ t₅ ∧ t₂ = t₅ ++ t₄ := by
  rw [← toSlice_lt, (splits_toSlice_iff.2 h).lt_iff_exists_eq_append (splits_toSlice_iff.2 h')]

-- TODO
theorem Pos.Raw.isValidForSlice_iff_exists_append {s : Slice} {p : Pos.Raw} :
    p.IsValidForSlice s ↔ ∃ t₁ t₂, s.copy = t₁ ++ t₂ ∧ p = t₁.rawEndPos := by
  rw [← isValid_copy_iff, isValid_iff_exists_append]

def Slice.Pos.Splits.rotateRight {s : Slice} {p : s.Pos} {t₁ t₂ t₃ : String}
    (h : p.Splits t₁ (t₂ ++ t₃)) : s.Pos :=
  s.pos (p.offset.increaseBy t₂.utf8ByteSize)
    (Pos.Raw.isValidForSlice_iff_exists_append.2
      ⟨t₁ ++ t₂, t₃, by simpa [append_assoc] using h.eq_append,
        by simp [Pos.Raw.ext_iff, h.offset_eq_rawEndPos]⟩)

theorem Slice.Pos.Splits.splits_rotateRight {s : Slice} {p : s.Pos} {t₁ t₂ t₃ : String}
    (h : p.Splits t₁ (t₂ ++ t₃)) : h.rotateRight.Splits (t₁ ++ t₂) t₃ where
  eq_append := by simpa [append_assoc] using h.eq_append
  offset_eq_rawEndPos := by simp [rotateRight, Pos.Raw.ext_iff, h.offset_eq_rawEndPos]

theorem Slice.copy_slice_eq_iff_splits {s : Slice} {pos₁ pos₂ : s.Pos} :
    (∃ h, (s.slice pos₁ pos₂ h).copy = t) ↔
    ∃ t₁ t₂, pos₁.Splits t₁ (t ++ t₂) ∧ pos₂.Splits (t₁ ++ t) t₂ := by
  refine ⟨?_, fun ⟨t₁, t₂, ht₁, ht₂⟩ => ?_⟩
  · rintro ⟨h, rfl⟩
    refine ⟨(s.sliceTo pos₁).copy, (s.sliceFrom pos₂).copy,
      ⟨by simpa [append_assoc] using copy_eq_copy_slice, by simp⟩, ⟨copy_eq_copy_slice, ?_⟩⟩
    simp [Pos.Raw.ext_iff, Slice.Pos.le_iff, Pos.Raw.le_iff, Pos.Raw.byteDistance_eq] at ⊢ h
    omega
  · have h : pos₁ ≤ pos₂ := (ht₁.le_iff_exists_eq_append ht₂).2 ⟨t, rfl, rfl⟩
    exact ⟨h, by simpa [ht₂.eq_append, ht₁.eq_left pos₁.splits, ht₂.eq_right pos₂.splits] using
      (copy_eq_copy_slice (h := h)).symm⟩

end String
