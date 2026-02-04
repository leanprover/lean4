/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

prelude
public import Init.Data.String.FindPos
import all Init.Data.String.FindPos
import Init.Data.String.OrderInstances
import Init.Data.String.Lemmas.Basic
import Init.Data.String.Lemmas.Order

public section

namespace String

namespace Slice

@[simp]
theorem le_offset_posGE {s : Slice} {p : Pos.Raw} {h : p ≤ s.rawEndPos} :
    p ≤ (s.posGE p h).offset := by
  fun_induction posGE with
  | case1 => simp
  | case2 => exact Std.le_trans (Std.le_of_lt (Pos.Raw.lt_inc)) ‹_›
  | case3 => assumption

@[simp]
theorem posGE_le_iff {s : Slice} {p : Pos.Raw} {h : p ≤ s.rawEndPos} {q : s.Pos} :
    s.posGE p h ≤ q ↔ p ≤ q.offset := by
  fun_induction posGE with
  | case1 => simp [Pos.le_iff]
  | case2 r h₁ h₂ h₃ ih =>
    suffices r ≠ q.offset by simp [ih, Pos.Raw.inc_le, Std.le_iff_lt_or_eq (a := r), this]
    exact fun h => h₃ (h ▸ q.isUTF8FirstByte_getUTF8Byte_offset)
  | case3 r h₁ h₂ =>
    obtain rfl : r = s.rawEndPos := Std.le_antisymm h₁ (Std.not_lt.1 h₂)
    simp only [Pos.endPos_le, ← offset_endPos, ← Pos.le_iff]

@[simp]
theorem lt_posGE_iff {s : Slice} {p : Pos.Raw} {h : p ≤ s.rawEndPos} {q : s.Pos} :
    q < s.posGE p h ↔ q.offset < p := by
  rw [← Std.not_le, posGE_le_iff, Std.not_le]

theorem posGE_eq_iff {s : Slice} {p : Pos.Raw} {h : p ≤ s.rawEndPos} {q : s.Pos} :
    s.posGE p h = q ↔ p ≤ q.offset ∧ ∀ q', p ≤ q'.offset → q ≤ q' :=
  ⟨by rintro rfl; simp, fun ⟨h₁, h₂⟩ => Std.le_antisymm (by simpa) (h₂ _ (by simp))⟩

theorem posGT_eq_posGE {s : Slice} {p : Pos.Raw} {h : p < s.rawEndPos} :
    s.posGT p h = s.posGE p.inc (by simpa) :=
  (rfl)

@[simp]
theorem posGE_inc {s : Slice} {p : Pos.Raw} {h : p.inc ≤ s.rawEndPos} :
    s.posGE p.inc h = s.posGT p (by simpa) :=
  (rfl)

@[simp]
theorem lt_offset_posGT {s : Slice} {p : Pos.Raw} {h : p < s.rawEndPos} :
    p < (s.posGT p h).offset :=
  Std.lt_of_lt_of_le p.lt_inc (by simp [posGT_eq_posGE, -posGE_inc])

@[simp]
theorem posGT_le_iff {s : Slice} {p : Pos.Raw} {h : p < s.rawEndPos} {q : s.Pos} :
    s.posGT p h ≤ q ↔ p < q.offset := by
  rw [posGT_eq_posGE, posGE_le_iff, Pos.Raw.inc_le]

@[simp]
theorem lt_posGT_iff {s : Slice} {p : Pos.Raw} {h : p < s.rawEndPos} {q : s.Pos} :
    q < s.posGT p h ↔ q.offset ≤ p := by
  rw [posGT_eq_posGE, lt_posGE_iff, Pos.Raw.lt_inc_iff]

theorem posGT_eq_iff {s : Slice} {p : Pos.Raw} {h : p < s.rawEndPos} {q : s.Pos} :
    s.posGT p h = q ↔ p < q.offset ∧ ∀ q', p < q'.offset → q ≤ q' := by
  simp [posGT_eq_posGE, -posGE_inc, posGE_eq_iff]

@[simp]
theorem Pos.posGE_offset {s : Slice} {p : s.Pos} : s.posGE p.offset (by simp) = p := by
  simp [posGE_eq_iff, Pos.le_iff]

@[simp]
theorem offset_posGE_eq_self_iff {s : Slice} {p : String.Pos.Raw} {h} :
    (s.posGE p h).offset = p ↔ p.IsValidForSlice s :=
  ⟨fun h' => by simpa [h'] using (s.posGE p h).isValidForSlice,
   fun h' => by simpa using congrArg Pos.offset (Pos.posGE_offset (p := s.pos p h'))⟩

theorem posGE_eq_pos {s : Slice} {p : String.Pos.Raw} (h : p.IsValidForSlice s) :
    s.posGE p h.le_rawEndPos = s.pos p h := by
  simpa using Pos.posGE_offset (p := s.pos p h)

theorem pos_eq_posGE {s : Slice} {p : String.Pos.Raw} {h} :
    s.pos p h = s.posGE p h.le_rawEndPos := by
  simp [posGE_eq_pos h]

@[simp]
theorem Pos.posGT_offset {s : Slice} {p : s.Pos} {h} :
    s.posGT p.offset h = p.next (by simpa using h) := by
  rw [posGT_eq_iff, ← Pos.lt_iff]
  simp [← Pos.lt_iff]

theorem posGT_eq_next {s : Slice} {p : String.Pos.Raw} {h} (h' : p.IsValidForSlice s) :
    s.posGT p h = (s.pos p h').next (by simpa [Pos.ext_iff] using Pos.Raw.ne_of_lt h) := by
  simpa using Pos.posGT_offset (h := h) (p := s.pos p h')

theorem next_eq_posGT {s : Slice} {p : s.Pos} {h} :
    p.next h = s.posGT p.offset (by simpa) := by
  simp

end Slice

@[simp]
theorem le_offset_posGE {s : String} {p : Pos.Raw} {h : p ≤ s.rawEndPos} :
    p ≤ (s.posGE p h).offset := by
  simp [posGE]

@[simp]
theorem posGE_le_iff {s : String} {p : Pos.Raw} {h : p ≤ s.rawEndPos} {q : s.Pos} :
    s.posGE p h ≤ q ↔ p ≤ q.offset := by
  simp [posGE, Pos.ofToSlice_le_iff]

@[simp]
theorem lt_posGE_iff {s : String} {p : Pos.Raw} {h : p ≤ s.rawEndPos} {q : s.Pos} :
    q < s.posGE p h ↔ q.offset < p := by
  simp [posGE, Pos.lt_ofToSlice_iff]

theorem posGE_eq_iff {s : String} {p : Pos.Raw} {h : p ≤ s.rawEndPos} {q : s.Pos} :
    s.posGE p h = q ↔ p ≤ q.offset ∧ ∀ q', p ≤ q'.offset → q ≤ q' :=
  ⟨by rintro rfl; simp, fun ⟨h₁, h₂⟩ => Std.le_antisymm (by simpa) (h₂ _ (by simp))⟩

theorem posGT_eq_posGE {s : String} {p : Pos.Raw} {h : p < s.rawEndPos} :
    s.posGT p h = s.posGE p.inc (by simpa) :=
  (rfl)

@[simp]
theorem posGE_inc {s : String} {p : Pos.Raw} {h : p.inc ≤ s.rawEndPos} :
    s.posGE p.inc h = s.posGT p (by simpa) :=
  (rfl)

@[simp]
theorem lt_offset_posGT {s : String} {p : Pos.Raw} {h : p < s.rawEndPos} :
    p < (s.posGT p h).offset :=
  Std.lt_of_lt_of_le p.lt_inc (by simp [posGT_eq_posGE, -posGE_inc])

@[simp]
theorem posGT_le_iff {s : String} {p : Pos.Raw} {h : p < s.rawEndPos} {q : s.Pos} :
    s.posGT p h ≤ q ↔ p < q.offset := by
  rw [posGT_eq_posGE, posGE_le_iff, Pos.Raw.inc_le]

@[simp]
theorem lt_posGT_iff {s : String} {p : Pos.Raw} {h : p < s.rawEndPos} {q : s.Pos} :
    q < s.posGT p h ↔ q.offset ≤ p := by
  rw [posGT_eq_posGE, lt_posGE_iff, Pos.Raw.lt_inc_iff]

theorem posGT_eq_iff {s : String} {p : Pos.Raw} {h : p < s.rawEndPos} {q : s.Pos} :
    s.posGT p h = q ↔ p < q.offset ∧ ∀ q', p < q'.offset → q ≤ q' := by
  simp [posGT_eq_posGE, -posGE_inc, posGE_eq_iff]

theorem posGE_toSlice {s : String} {p : Pos.Raw} (h : p ≤ s.toSlice.rawEndPos) :
    s.toSlice.posGE p h = (s.posGE p (by simpa)).toSlice := by
  simp [posGE]

theorem posGE_eq_posGE_toSlice {s : String} {p : Pos.Raw} (h : p ≤ s.rawEndPos) :
    s.posGE p h = Pos.ofToSlice (s.toSlice.posGE p (by simpa)) := by
  simp [posGE]

theorem posGT_toSlice {s : String} {p : Pos.Raw} (h : p < s.toSlice.rawEndPos) :
    s.toSlice.posGT p h = (s.posGT p (by simpa)).toSlice := by
  simp [posGT]

theorem posGT_eq_posGT_toSlice {s : String} {p : Pos.Raw} (h : p < s.rawEndPos) :
    s.posGT p h = Pos.ofToSlice (s.toSlice.posGT p (by simpa)) := by
  simp [posGT]

@[simp]
theorem Pos.posGE_offset {s : String} {p : s.Pos} : s.posGE p.offset (by simp) = p := by
  simp [posGE_eq_iff, Pos.le_iff]

@[simp]
theorem offset_posGE_eq_self_iff {s : String} {p : String.Pos.Raw} {h} :
    (s.posGE p h).offset = p ↔ p.IsValid s :=
  ⟨fun h' => by simpa [h'] using (s.posGE p h).isValid,
   fun h' => by simpa using congrArg Pos.offset (Pos.posGE_offset (p := s.pos p h'))⟩

theorem posGE_eq_pos {s : String} {p : String.Pos.Raw} (h : p.IsValid s) :
    s.posGE p h.le_rawEndPos = s.pos p h := by
  simpa using Pos.posGE_offset (p := s.pos p h)

theorem pos_eq_posGE {s : String} {p : String.Pos.Raw} {h} :
    s.pos p h = s.posGE p h.le_rawEndPos := by
  simp [posGE_eq_pos h]

@[simp]
theorem Pos.posGT_offset {s : String} {p : s.Pos} {h} :
    s.posGT p.offset h = p.next (by simpa using h) := by
  rw [posGT_eq_iff, ← Pos.lt_iff]
  simp [← Pos.lt_iff]

theorem posGT_eq_next {s : String} {p : String.Pos.Raw} {h} (h' : p.IsValid s) :
    s.posGT p h = (s.pos p h').next (by simpa [Pos.ext_iff] using Pos.Raw.ne_of_lt h) := by
  simpa using Pos.posGT_offset (h := h) (p := s.pos p h')

theorem next_eq_posGT {s : String} {p : s.Pos} {h} :
    p.next h = s.posGT p.offset (by simpa) := by
  simp

end String
