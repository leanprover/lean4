/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julia M. Himmel
-/
module

prelude
public import Init.Data.String.Defs
public import Init.Data.Char.Basic
public import Init.Data.Ord.Basic
public import Init.Data.Ord.UInt
public import Init.Data.ByteArray.Lex
public import Init.Data.String.Basic
import Init.Data.List.Lemmas
import Init.Data.List.Basic
import Init.Data.List.Lex
import Init.Data.Order.Lemmas
import Init.Data.Order.LemmasExtra
import Init.Data.List.Sublist
import Init.Data.String.Decode
import Init.Omega
import Init.Data.UInt.Lemmas
import Init.Data.String.Basic
import Init.Data.ByteArray.Lex
import Init.Data.Char.Order
import Init.Data.BitVec.Package
import Init.Data.List.Package
import Init.Data.Char.Lemmas
import Init.Data.BitVec.Lemmas
import all Init.Data.String.Decode

/-! # Further results about UTF-8 decoding -/

theorem Char.utf8Size_le_of_le {c d : Char} (h : c ≤ d) : c.utf8Size ≤ d.utf8Size := by
  rw [Char.le_def, UInt32.le_iff_toNat_le] at h
  obtain (hc|hc|hc|hc) := c.utf8Size_eq <;>
    obtain (hd|hd|hd|hd) := d.utf8Size_eq <;>
      simp only [hc, hd]
  all_goals
    simp only [Char.utf8Size_eq_one_iff, Char.utf8Size_eq_two_iff, Char.utf8Size_eq_three_iff,
      Char.utf8Size_eq_four_iff, UInt32.le_iff_toNat_le, UInt32.lt_iff_toNat_lt,
      UInt32.reduceToNat] at hc hd
    omega

namespace String

/-- UTF-8 is a prefix code: if `c` encodes to a prefix of `d`, then we must have `c = d`. -/
theorem eq_of_utf8EncodeChar_prefix {c d : Char}
    (h : String.utf8EncodeChar c <+: String.utf8EncodeChar d) : c = d := by
  suffices c.utf8Size = d.utf8Size from String.utf8EncodeChar_inj (h.eq_of_length
    (length_utf8EncodeChar c ▸ length_utf8EncodeChar d ▸ this))
  rw [← Char.utf8ByteSize_getElem_utf8EncodeChar]
  simp only [h.getElem, Char.utf8ByteSize_getElem_utf8EncodeChar]

theorem helper {c d : Char} {w w' : Nat} (hw : w ≤ 8) (hw' : w' ≤ 8) {b : BitVec w}
    {a : BitVec (8 - w)} {b' : BitVec w'} {a' : BitVec (8 - w')}
    (h₁ : ((String.utf8EncodeChar c)[0]'(by simp [Char.utf8Size_pos])).toBitVec =
      (b ++ a).cast (by omega))
    (h₂ : ((String.utf8EncodeChar d)[0]'(by simp [Char.utf8Size_pos])).toBitVec =
      (b' ++ a').cast (by omega))
    (len : Nat) (hl₁ : len ≤ w := by omega) (hl₂ : len ≤ w' := by omega)
    (hlt : b.extractLsb' (w - len) len < b'.extractLsb' (w' - len) len := by simp) :
    String.utf8EncodeChar c < String.utf8EncodeChar d := by
  apply List.lt_of_getElem_zero (by simp [Char.utf8Size_pos]) (by simp [Char.utf8Size_pos])
  rw [UInt8.lt_iff_toBitVec_lt, h₁, h₂]
  apply BitVec.lt_of_lt_extractLsb' len
  rwa [BitVec.extractLsb'_cast, BitVec.extractLsb'_cast,
    BitVec.extractLsb'_append_eq_of_le (by omega), BitVec.extractLsb'_append_eq_of_le (by omega),
    show 8 - len - (8 - w) = w - len by omega, show 8 - len - (8 - w') = w' - len by omega]

theorem utf8EncodeChar_lt_utf8EncodeChar_of_utf8Size_lt {c d : Char} (h : c.utf8Size < d.utf8Size) :
    String.utf8EncodeChar c < String.utf8EncodeChar d :=
  match hc : c.utf8Size, hd : d.utf8Size, c.utf8Size_pos, h, d.utf8Size_le_four with
  | 1, 2, _, _, _ => helper (by omega) (by omega)
      (String.toBitVec_getElem_utf8EncodeChar_zero_of_utf8Size_eq_one hc)
      (String.toBitVec_getElem_utf8EncodeChar_zero_of_utf8Size_eq_two hd) 1
  | 1, 3, _, _, _ => helper (by omega) (by omega)
      (String.toBitVec_getElem_utf8EncodeChar_zero_of_utf8Size_eq_one hc)
      (String.toBitVec_getElem_utf8EncodeChar_zero_of_utf8Size_eq_three hd) 1
  | 1, 4, _, _, _ => helper (by omega) (by omega)
      (String.toBitVec_getElem_utf8EncodeChar_zero_of_utf8Size_eq_one hc)
      (String.toBitVec_getElem_utf8EncodeChar_zero_of_utf8Size_eq_four hd) 1
  | 2, 3, _, _, _ => helper (by omega) (by omega)
      (String.toBitVec_getElem_utf8EncodeChar_zero_of_utf8Size_eq_two hc)
      (String.toBitVec_getElem_utf8EncodeChar_zero_of_utf8Size_eq_three hd) 3
  | 2, 4, _, _, _ => helper (by omega) (by omega)
      (String.toBitVec_getElem_utf8EncodeChar_zero_of_utf8Size_eq_two hc)
      (String.toBitVec_getElem_utf8EncodeChar_zero_of_utf8Size_eq_four hd) 3
  | 3, 4, _, _, _ => helper (by omega) (by omega)
      (String.toBitVec_getElem_utf8EncodeChar_zero_of_utf8Size_eq_three hc)
      (String.toBitVec_getElem_utf8EncodeChar_zero_of_utf8Size_eq_four hd) 4
  | n+4, _, _, _, _ => by omega

theorem utf8EncodeChar_lt_utf8EncodeChar {c d : Char} (h : c < d) :
    String.utf8EncodeChar c < String.utf8EncodeChar d := by
  obtain (h₁|h₁) := Std.le_iff_lt_or_eq.1 (Char.utf8Size_le_of_le (Std.le_of_lt h))
  · exact String.utf8EncodeChar_lt_utf8EncodeChar_of_utf8Size_lt h₁
  · rw [← List.map_lt_map_iff UInt8.toBitVec (by simp [UInt8.lt_iff_toBitVec_lt]),
      ← Std.compare_eq_lt]
    rw [Char.lt_def, UInt32.lt_iff_toBitVec_lt, ← Std.compare_eq_lt] at h
    obtain (hc|hc|hc|hc) := c.utf8Size_eq <;> have hd := h₁ ▸ hc
    all_goals
      simp +singlePass (discharger := omega) only [
        Char.toBitVec_val_of_utf8Size_eq_one,
        Char.toBitVec_val_of_utf8Size_eq_two,
        Char.toBitVec_val_of_utf8Size_eq_three,
        Char.toBitVec_val_of_utf8Size_eq_four,
        BitVec.compare_setWidth_setWidth_of_le] at h
      simp (discharger := assumption) only [
        String.map_toBitVec_utf8EncodeChar_of_utf8Size_eq_one,
        String.map_toBitVec_utf8EncodeChar_of_utf8Size_eq_two,
        String.map_toBitVec_utf8EncodeChar_of_utf8Size_eq_three,
        String.map_toBitVec_utf8EncodeChar_of_utf8Size_eq_four,
        BitVec.compare_append_append,
        Nat.reduceAdd,
        List.compare_cons_cons,
        Std.compare_self,
        Ordering.eq_then,
        Ordering.then_eq]
      simpa (discharger := omega) only [← BitVec.compare_append_append,
        BitVec.extractLsb'_append_extractLsb'_eq_extractLsb']

theorem utf8EncodeChar_le_utf8EncodeChar {c d : Char} (h : c ≤ d) :
    String.utf8EncodeChar c ≤ String.utf8EncodeChar d := by
  obtain (h|rfl) := Std.le_iff_lt_or_eq.1 h
  · exact Std.le_of_lt (String.utf8EncodeChar_lt_utf8EncodeChar h)
  · exact Std.le_refl _

theorem lt_of_utf8EncodeChar_lt_utf8EncodeChar {c d : Char}
    (h : String.utf8EncodeChar c < String.utf8EncodeChar d) : c < d := by
  obtain (hc|rfl|hc) := Std.lt_trichotomy c d
  · exact hc
  · simp [Std.lt_irrefl] at h
  · exact False.elim (Std.not_gt_of_lt h (String.utf8EncodeChar_lt_utf8EncodeChar hc))

@[simp]
public theorem utf8EncodeChar_lt_utf8EncodeChar_iff {c d : Char} :
    String.utf8EncodeChar c < String.utf8EncodeChar d ↔ c < d :=
  ⟨String.lt_of_utf8EncodeChar_lt_utf8EncodeChar, String.utf8EncodeChar_lt_utf8EncodeChar⟩

@[simp]
public theorem compare_utf8EncodeChar_utf8EncodeChar {c d : Char} :
    compare (String.utf8EncodeChar c) (String.utf8EncodeChar d) = compare c d := by
  apply Std.compare_eq_of_lt_iff
  · simp [Std.compare_eq_lt]
  · simp [Std.compare_eq_gt]

@[simp]
public theorem utf8EncodeChar_le_utf8EncodeChar_iff {c d : Char} :
    String.utf8EncodeChar c ≤ String.utf8EncodeChar d ↔ c ≤ d := by
  simp [← Std.isLE_compare]

public theorem compare_toList_toList_eq_compare_toByteArray_toByteArray {s t : String} :
    compare s.toList t.toList = compare s.toByteArray t.toByteArray := by
  obtain ⟨c, rfl⟩ := s.exists_eq_ofList
  obtain ⟨d, rfl⟩ := t.exists_eq_ofList
  simp only [toList_ofList, toByteArray_ofList, List.utf8Encode,
    List.compare_toByteArray_toByteArray]
  rw [List.compare_flatMap_flatMap _ (by simp) _ (by simp)]
  exact fun a b => String.eq_of_utf8EncodeChar_prefix

public theorem toList_lt_toList_iff_toByteArray_lt_toByteArray {s t : String} :
    s.toList < t.toList ↔ s.toByteArray < t.toByteArray := by
  simp [← Std.compare_eq_lt, compare_toList_toList_eq_compare_toByteArray_toByteArray]

public theorem toList_le_toList_iff_toByteArray_le_toByteArray {s t : String} :
    s.toList ≤ t.toList ↔ s.toByteArray ≤ t.toByteArray := by
  simp [← Std.isLE_compare, compare_toList_toList_eq_compare_toByteArray_toByteArray]

end String
