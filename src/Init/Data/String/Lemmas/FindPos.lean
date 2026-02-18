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
import Init.Data.String.Lemmas.Order
import Init.Data.Order.Lemmas

public section

namespace String

namespace Slice

@[simp]
theorem le_offset_posGE {s : Slice} {p : Pos.Raw} {h : p ≤ s.rawEndPos} :
    p ≤ (s.posGE p h).offset := by
  fun_induction posGE with
  | case1 => simp
  | case2 => exact Std.le_trans (Std.le_of_lt (Pos.Raw.lt_inc)) ‹_›

@[simp]
theorem posGE_le_iff {s : Slice} {p : Pos.Raw} {h : p ≤ s.rawEndPos} {q : s.Pos} :
    s.posGE p h ≤ q ↔ p ≤ q.offset := by
  fun_induction posGE with
  | case1 => simp [Pos.le_iff]
  | case2 r h₁ h₂ h₃ ih =>
    suffices r ≠ q.offset by simp [ih, Pos.Raw.inc_le, Std.le_iff_lt_or_eq (a := r), this]
    exact fun h => by simp [h, q.isValidForSlice] at h₂

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

theorem Pos.next_eq_posGT {s : Slice} {p : s.Pos} {h} :
    p.next h = s.posGT p.offset (by simpa) := by
  simp

@[simp]
theorem offset_posLE_le {s : Slice} {p : Pos.Raw} : (s.posLE p).offset ≤ p := by
  fun_induction posLE with
  | case1 => simp
  | case2 => exact Std.le_trans ‹_› (Std.le_of_lt (Pos.Raw.dec_lt ‹_›))

@[simp]
theorem le_posLE_iff {s : Slice} {p : s.Pos} {q : Pos.Raw} :
    p ≤ s.posLE q ↔ p.offset ≤ q := by
  fun_induction posLE with
  | case1 => simp [Pos.le_iff]
  | case2 r h₁ h₂ ih =>
    suffices p.offset ≠ r by simp [ih, Pos.Raw.le_dec h₂, Std.le_iff_lt_or_eq (b := r), this]
    exact fun h => by simp [← h, p.isValidForSlice] at h₁

@[simp]
theorem posLE_lt_iff {s : Slice} {p : s.Pos} {q : Pos.Raw} :
    s.posLE q < p ↔ q < p.offset := by
  rw [← Std.not_le, le_posLE_iff, Std.not_le]

theorem posLE_eq_iff {s : Slice} {p : Pos.Raw} {q : s.Pos} :
    s.posLE p = q ↔ q.offset ≤ p ∧ ∀ q', q'.offset ≤ p → q' ≤ q :=
  ⟨by rintro rfl; simp, fun ⟨h₁, h₂⟩ => Std.le_antisymm (h₂ _ (by simp)) (by simpa)⟩

theorem posLT_eq_posLE {s : Slice} {p : Pos.Raw} {h : 0 < p} :
    s.posLT p h = s.posLE p.dec := (rfl)

theorem posLE_dec {s : Slice} {p : Pos.Raw} (h : 0 < p) :
    s.posLE p.dec = s.posLT p h := (rfl)

@[simp]
theorem offset_posLT_lt {s : Slice} {p : Pos.Raw} {h : 0 < p} :
    (s.posLT p h).offset < p :=
  Std.lt_of_le_of_lt (by simp [posLT_eq_posLE]) (Pos.Raw.dec_lt (Pos.Raw.pos_iff_ne_zero.1 h))

@[simp]
theorem le_posLT_iff {s : Slice} {p : Pos.Raw} {h : 0 < p} {q : s.Pos} :
    q ≤ s.posLT p h ↔ q.offset < p := by
  rw [posLT_eq_posLE, le_posLE_iff, Pos.Raw.le_dec (Pos.Raw.pos_iff_ne_zero.1 h)]

@[simp]
theorem posLT_lt_iff {s : Slice} {p : Pos.Raw} {h : 0 < p} {q : s.Pos} :
    s.posLT p h < q ↔ p ≤ q.offset := by
  rw [posLT_eq_posLE, posLE_lt_iff, Pos.Raw.dec_lt_iff (Pos.Raw.pos_iff_ne_zero.1 h)]

theorem posLT_eq_iff {s : Slice} {p : Pos.Raw} {h : 0 < p} {q : s.Pos} :
    s.posLT p h = q ↔ q.offset < p ∧ ∀ q', q'.offset < p → q' ≤ q := by
  simp [posLT_eq_posLE, posLE_eq_iff, Pos.Raw.le_dec (Pos.Raw.pos_iff_ne_zero.1 h)]

@[simp]
theorem Pos.posLE_offset {s : Slice} {p : s.Pos} : s.posLE p.offset = p := by
  simp [posLE_eq_iff, Pos.le_iff]

@[simp]
theorem offset_posLE_eq_self_iff {s : Slice} {p : String.Pos.Raw} :
    (s.posLE p).offset = p ↔ p.IsValidForSlice s :=
  ⟨fun h' => by simpa [h'] using (s.posLE p).isValidForSlice,
   fun h' => by simpa using congrArg Pos.offset (Pos.posLE_offset (p := s.pos p h'))⟩

theorem posLE_eq_pos {s : Slice} {p : String.Pos.Raw} (h : p.IsValidForSlice s) :
    s.posLE p = s.pos p h := by
  simpa using Pos.posLE_offset (p := s.pos p h)

theorem pos_eq_posLE {s : Slice} {p : String.Pos.Raw} {h} :
    s.pos p h = s.posLE p := by
  simp [posLE_eq_pos h]

@[simp]
theorem Pos.posLT_offset {s : Slice} {p : s.Pos} {h} :
    s.posLT p.offset h = p.prev (by simpa [Pos.Raw.pos_iff_ne_zero, Pos.ext_iff] using h) := by
  simp [prev]

theorem posLT_eq_prev {s : Slice} {p : String.Pos.Raw} {h} (h' : p.IsValidForSlice s) :
    s.posLT p h = (s.pos p h').prev (by simpa [Pos.Raw.pos_iff_ne_zero, Pos.ext_iff] using h) := by
  simpa using Pos.posLT_offset (h := h) (p := s.pos p h')

theorem Pos.prev_eq_posLT {s : Slice} {p : s.Pos} {h} :
    p.prev h = s.posLT p.offset (by simpa [Pos.Raw.pos_iff_ne_zero, Pos.ext_iff] using h) := by
  simp

@[simp]
theorem Pos.le_prev_iff_lt {s : Slice} {p q : s.Pos} {h} : p ≤ q.prev h ↔ p < q := by
  simp [prev_eq_posLT, -posLT_offset, Pos.lt_iff]

@[simp]
theorem Pos.prev_lt_iff_le {s : Slice} {p q : s.Pos} {h} : p.prev h < q ↔ p ≤ q := by
  simp [prev_eq_posLT, -posLT_offset, Pos.le_iff]

theorem Pos.prev_eq_iff {s : Slice} {p q : s.Pos} {h} :
    p.prev h = q ↔ q < p ∧ ∀ q', q' < p → q' ≤ q := by
  simp only [prev_eq_posLT, posLT_eq_iff, Pos.lt_iff]

@[simp]
theorem Pos.prev_lt {s : Slice} {p : s.Pos} {h} : p.prev h < p := by
  simp

@[simp]
theorem Pos.prev_ne_endPos {s : Slice} {p : s.Pos} {h} : p.prev h ≠ s.endPos :=
  ne_endPos_of_lt prev_lt

theorem Pos.prevn_le {s : Slice} {p : s.Pos} {n : Nat} : p.prevn n ≤ p := by
  fun_induction prevn with
  | case1 => simp
  | case2 p n h ih => exact Std.le_of_lt (by simpa using ih)
  | case3 => simp

@[simp]
theorem Pos.prev_next {s : Slice} {p : s.Pos} {h} : (p.next h).prev (by simp) = p :=
  prev_eq_iff.2 (by simp)

@[simp]
theorem Pos.next_prev {s : Slice} {p : s.Pos} {h} : (p.prev h).next (by simp) = p :=
  next_eq_iff.2 (by simp)

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

@[simp]
theorem offset_posLE_le {s : String} {p : Pos.Raw} : (s.posLE p).offset ≤ p := by
  simp [posLE]

@[simp]
theorem le_posLE_iff {s : String} {p : s.Pos} {q : Pos.Raw} :
    p ≤ s.posLE q ↔ p.offset ≤ q := by
  simp [posLE, Pos.le_ofToSlice_iff]

@[simp]
theorem posLE_lt_iff {s : String} {p : s.Pos} {q : Pos.Raw} :
    s.posLE q < p ↔ q < p.offset := by
  rw [← Std.not_le, le_posLE_iff, Std.not_le]

theorem posLE_eq_iff {s : String} {p : Pos.Raw} {q : s.Pos} :
    s.posLE p = q ↔ q.offset ≤ p ∧ ∀ q', q'.offset ≤ p → q' ≤ q :=
  ⟨by rintro rfl; simp, fun ⟨h₁, h₂⟩ => Std.le_antisymm (h₂ _ (by simp)) (by simpa)⟩

theorem posLT_eq_posLE {s : String} {p : Pos.Raw} {h : 0 < p} :
    s.posLT p h = s.posLE p.dec := (rfl)

theorem posLE_dec {s : String} {p : Pos.Raw} (h : 0 < p) :
    s.posLE p.dec = s.posLT p h := (rfl)

@[simp]
theorem offset_posLT_lt {s : String} {p : Pos.Raw} {h : 0 < p} :
    (s.posLT p h).offset < p :=
  Std.lt_of_le_of_lt (by simp [posLT_eq_posLE]) (Pos.Raw.dec_lt (Pos.Raw.pos_iff_ne_zero.1 h))

@[simp]
theorem le_posLT_iff {s : String} {p : Pos.Raw} {h : 0 < p} {q : s.Pos} :
    q ≤ s.posLT p h ↔ q.offset < p := by
  rw [posLT_eq_posLE, le_posLE_iff, Pos.Raw.le_dec (Pos.Raw.pos_iff_ne_zero.1 h)]

@[simp]
theorem posLT_lt_iff {s : String} {p : Pos.Raw} {h : 0 < p} {q : s.Pos} :
    s.posLT p h < q ↔ p ≤ q.offset := by
  rw [posLT_eq_posLE, posLE_lt_iff, Pos.Raw.dec_lt_iff (Pos.Raw.pos_iff_ne_zero.1 h)]

theorem posLT_eq_iff {s : String} {p : Pos.Raw} {h : 0 < p} {q : s.Pos} :
    s.posLT p h = q ↔ q.offset < p ∧ ∀ q', q'.offset < p → q' ≤ q := by
  simp [posLT_eq_posLE, posLE_eq_iff, Pos.Raw.le_dec (Pos.Raw.pos_iff_ne_zero.1 h)]

theorem posLE_toSlice {s : String} {p : Pos.Raw} :
    s.toSlice.posLE p = (s.posLE p).toSlice := by
  simp [posLE]

theorem posLE_eq_posLE_toSlice {s : String} {p : Pos.Raw} :
    s.posLE p = Pos.ofToSlice (s.toSlice.posLE p) := by
  simp [posLE]

theorem posLT_toSlice {s : String} {p : Pos.Raw} (h : 0 < p) :
    s.toSlice.posLT p h = (s.posLT p h).toSlice := by
  simp [posLT]

theorem posLT_eq_posLT_toSlice {s : String} {p : Pos.Raw} (h : 0 < p) :
    s.posLT p h = Pos.ofToSlice (s.toSlice.posLT p h) := by
  simp [posLT]

@[simp]
theorem Pos.posLE_offset {s : String} {p : s.Pos} : s.posLE p.offset = p := by
  simp [posLE_eq_iff, Pos.le_iff]

@[simp]
theorem offset_posLE_eq_self_iff {s : String} {p : String.Pos.Raw} :
    (s.posLE p).offset = p ↔ p.IsValid s :=
  ⟨fun h' => by simpa [h'] using (s.posLE p).isValid,
   fun h' => by simpa using congrArg Pos.offset (Pos.posLE_offset (p := s.pos p h'))⟩

theorem posLE_eq_pos {s : String} {p : String.Pos.Raw} (h : p.IsValid s) :
    s.posLE p = s.pos p h := by
  simpa using Pos.posLE_offset (p := s.pos p h)

theorem pos_eq_posLE {s : String} {p : String.Pos.Raw} {h} :
    s.pos p h = s.posLE p := by
  simp [posLE_eq_pos h]

@[simp]
theorem Pos.posLT_offset {s : String} {p : s.Pos} {h} :
    s.posLT p.offset h = p.prev (by simpa [Pos.Raw.pos_iff_ne_zero, Pos.ext_iff] using h) := by
  simp [posLT, prev, Slice.Pos.prev, offset_toSlice]

theorem posLT_eq_prev {s : String} {p : String.Pos.Raw} {h} (h' : p.IsValid s) :
    s.posLT p h = (s.pos p h').prev (by simpa [Pos.Raw.pos_iff_ne_zero, Pos.ext_iff] using h) := by
  simpa using Pos.posLT_offset (h := h) (p := s.pos p h')

theorem Pos.prev_eq_posLT {s : String} {p : s.Pos} {h} :
    p.prev h = s.posLT p.offset (by simpa [Pos.Raw.pos_iff_ne_zero, Pos.ext_iff] using h) := by
  simp

@[simp]
theorem Pos.le_prev_iff_lt {s : String} {p q : s.Pos} {h} : p ≤ q.prev h ↔ p < q := by
  simp [prev_eq_posLT, -posLT_offset, Pos.lt_iff]

@[simp]
theorem Pos.prev_lt_iff_le {s : String} {p q : s.Pos} {h} : p.prev h < q ↔ p ≤ q := by
  simp [prev_eq_posLT, -posLT_offset, Pos.le_iff]

theorem Pos.prev_eq_iff {s : String} {p q : s.Pos} {h} :
    p.prev h = q ↔ q < p ∧ ∀ q', q' < p → q' ≤ q := by
  simp only [prev_eq_posLT, posLT_eq_iff, Pos.lt_iff]

@[simp]
theorem Pos.prev_lt {s : String} {p : s.Pos} {h} : p.prev h < p := by
  simp

@[simp]
theorem Pos.prev_ne_endPos {s : String} {p : s.Pos} {h} : p.prev h ≠ s.endPos :=
  ne_endPos_of_lt prev_lt

theorem Pos.toSlice_prev {s : String} {p : s.Pos} {h} :
    (p.prev h).toSlice = p.toSlice.prev (by simpa [toSlice_inj]) := by
  simp [prev]

theorem Pos.prev_toSlice {s : String} {p : s.Pos} {h} :
    p.toSlice.prev h = (p.prev (by simpa [← toSlice_inj])).toSlice := by
  simp [prev]

theorem Pos.prevn_le {s : String} {p : s.Pos} {n : Nat} :
    p.prevn n ≤ p := by
  simpa [Pos.le_iff, ← offset_toSlice] using Slice.Pos.prevn_le

@[simp]
theorem Pos.prev_next {s : String} {p : s.Pos} {h} : (p.next h).prev (by simp) = p :=
  prev_eq_iff.2 (by simp)

@[simp]
theorem Pos.next_prev {s : String} {p : s.Pos} {h} : (p.prev h).next (by simp) = p :=
  next_eq_iff.2 (by simp)

end String
