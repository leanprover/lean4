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
theorem lt_offset_posGT {s : Slice} {p : Pos.Raw} {h : p < s.rawEndPos} :
    p < (s.posGT p h).offset :=
  Std.lt_of_lt_of_le p.lt_inc (by simp [posGT_eq_posGE])

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
  simp [posGT_eq_posGE, posGE_eq_iff]

end Slice

end String
