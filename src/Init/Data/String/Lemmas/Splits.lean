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

/-!
# `Splits` predicates on `String.ValidPos` and `String.Slice.Pos`.

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
structure ValidPos.Splits {s : String} (p : s.ValidPos) (t₁ t₂ : String) : Prop where
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
theorem ValidPos.splits_cast_iff {s₁ s₂ : String} {h : s₁ = s₂} {p : s₁.ValidPos} {t₁ t₂ : String} :
    (p.cast h).Splits t₁ t₂ ↔ p.Splits t₁ t₂ := by
  subst h; simp

theorem ValidPos.Splits.cast {s₁ s₂ : String} {p : s₁.ValidPos} {t₁ t₂ : String} (h : s₁ = s₂) :
    p.Splits t₁ t₂ → (p.cast h).Splits t₁ t₂ :=
  splits_cast_iff.mpr

@[simp]
theorem Slice.Pos.splits_cast_iff {s₁ s₂ : Slice} {h : s₁ = s₂} {p : s₁.Pos} {t₁ t₂ : String} :
    (p.cast h).Splits t₁ t₂ ↔ p.Splits t₁ t₂ := by
  subst h; simp

theorem Slice.Pos.Splits.cast {s₁ s₂ : Slice} {p : s₁.Pos} {t₁ t₂ : String} (h : s₁ = s₂) :
    p.Splits t₁ t₂ → (p.cast h).Splits t₁ t₂ :=
  splits_cast_iff.mpr

theorem Slice.Pos.Splits.toCopy {s : Slice} {p : s.Pos} {t₁ t₂ : String}
    (h : p.Splits t₁ t₂) : p.toCopy.Splits t₁ t₂ where
  eq_append := h.eq_append
  offset_eq_rawEndPos := by simpa using h.offset_eq_rawEndPos

theorem Slice.Pos.splits_of_splits_toCopy {s : Slice} {p : s.Pos} {t₁ t₂ : String}
    (h : p.toCopy.Splits t₁ t₂) : p.Splits t₁ t₂ where
  eq_append := h.eq_append
  offset_eq_rawEndPos := by simpa using h.offset_eq_rawEndPos

@[simp]
theorem Slice.Pos.splits_toCopy_iff {s : Slice} {p : s.Pos} {t₁ t₂ : String} :
    p.toCopy.Splits t₁ t₂ ↔ p.Splits t₁ t₂ :=
  ⟨splits_of_splits_toCopy, (·.toCopy)⟩

@[simp]
theorem ValidPos.splits_toSlice_iff {s : String} {p : s.ValidPos} {t₁ t₂ : String} :
    p.toSlice.Splits t₁ t₂ ↔ p.Splits t₁ t₂ := by
  rw [← Slice.Pos.splits_toCopy_iff, p.toCopy_toSlice_eq_cast, splits_cast_iff]

theorem ValidPos.Splits.toSlice {s : String} {p : s.ValidPos} {t₁ t₂ : String}
    (h : p.Splits t₁ t₂) : p.toSlice.Splits t₁ t₂ :=
  splits_toSlice_iff.mpr h

theorem ValidPos.splits {s : String} (p : s.ValidPos) :
    p.Splits (s.replaceEnd p).copy (s.replaceStart p).copy where
  eq_append := by simp [← bytes_inj, Slice.bytes_copy, ← size_bytes]
  offset_eq_rawEndPos := by simp

theorem Slice.Pos.splits {s : Slice} (p : s.Pos) :
    p.Splits (s.replaceEnd p).copy (s.replaceStart p).copy where
  eq_append := copy_eq_copy_replaceEnd
  offset_eq_rawEndPos := by simp

theorem ValidPos.Splits.bytes_left_eq {s : String} {p : s.ValidPos} {t₁ t₂}
    (h : p.Splits t₁ t₂) : t₁.bytes = s.bytes.extract 0 p.offset.byteIdx := by
  simp [h.eq_append, h.offset_eq_rawEndPos, ByteArray.extract_append_eq_left]

theorem ValidPos.Splits.bytes_right_eq {s : String} {p : s.ValidPos} {t₁ t₂}
    (h : p.Splits t₁ t₂) : t₂.bytes = s.bytes.extract p.offset.byteIdx s.utf8ByteSize := by
  simp [h.eq_append, h.offset_eq_rawEndPos, ByteArray.extract_append_eq_right]

theorem ValidPos.Splits.eq_left {s : String} {p : s.ValidPos} {t₁ t₂ t₃ t₄}
    (h₁ : p.Splits t₁ t₂) (h₂ : p.Splits t₃ t₄) : t₁ = t₃ := by
  rw [← String.bytes_inj, h₁.bytes_left_eq, h₂.bytes_left_eq]

theorem ValidPos.Splits.eq_right {s : String} {p : s.ValidPos} {t₁ t₂ t₃ t₄}
    (h₁ : p.Splits t₁ t₂) (h₂ : p.Splits t₃ t₄) : t₂ = t₄ := by
  rw [← String.bytes_inj, h₁.bytes_right_eq, h₂.bytes_right_eq]

theorem ValidPos.Splits.eq {s : String} {p : s.ValidPos} {t₁ t₂ t₃ t₄}
    (h₁ : p.Splits t₁ t₂) (h₂ : p.Splits t₃ t₄) : t₁ = t₃ ∧ t₂ = t₄ :=
  ⟨h₁.eq_left h₂, h₁.eq_right h₂⟩

@[simp]
theorem splits_endValidPos (s : String) : s.endValidPos.Splits s "" where
  eq_append := by simp
  offset_eq_rawEndPos := by simp

@[simp]
theorem splits_endValidPos_iff {s : String} :
    s.endValidPos.Splits t₁ t₂ ↔ t₁ = s ∧ t₂ = "" :=
  ⟨fun h => ⟨h.eq_left s.splits_endValidPos, h.eq_right s.splits_endValidPos⟩,
   by rintro ⟨rfl, rfl⟩; exact t₁.splits_endValidPos⟩

theorem splits_startValidPos (s : String) : s.startValidPos.Splits "" s where
  eq_append := by simp
  offset_eq_rawEndPos := by simp

theorem ValidPos.splits_next_right {s : String} (p : s.ValidPos) (hp : p ≠ s.endValidPos) :
    p.Splits (s.replaceEnd p).copy (singleton (p.get hp) ++ (s.replaceStart (p.next hp)).copy) where
  eq_append := by simpa [← append_assoc] using p.eq_copy_replaceEnd_append_get hp
  offset_eq_rawEndPos := by simp

theorem ValidPos.splits_next {s : String} (p : s.ValidPos) (hp : p ≠ s.endValidPos) :
    (p.next hp).Splits ((s.replaceEnd p).copy ++ singleton (p.get hp)) (s.replaceStart (p.next hp)).copy where
  eq_append := p.eq_copy_replaceEnd_append_get hp
  offset_eq_rawEndPos := by simp

theorem ValidPos.Splits.exists_eq_singleton_append {s : String} {p : s.ValidPos}
    (hp : p ≠ s.endValidPos) (h : p.Splits t₁ t₂) : ∃ t₂', t₂ = singleton (p.get hp) ++ t₂' :=
  ⟨(s.replaceStart (p.next hp)).copy, h.eq_right (p.splits_next_right hp)⟩

theorem ValidPos.Splits.exists_eq_append_singleton {s : String} {p : s.ValidPos}
    (hp : p ≠ s.endValidPos) (h : (p.next hp).Splits t₁ t₂) : ∃ t₁', t₁ = t₁' ++ singleton (p.get hp) :=
  ⟨(s.replaceEnd p).copy, h.eq_left (p.splits_next hp)⟩

-- TODO: `hp` actually follows from `h`.
/-- You might want to invoke `ValidPos.Splits.exists_eq_singleton_append` to be able to apply this. -/
theorem ValidPos.Splits.next {s : String} {p : s.ValidPos} (h : p.Splits t₁ (singleton c ++ t₂))
    (hp : p ≠ s.endValidPos) : (p.next hp).Splits (t₁ ++ singleton c) t₂ := by
  obtain ⟨rfl, rfl, rfl⟩ := by simpa using h.eq (splits_next_right p hp)
  exact splits_next p hp

end String
