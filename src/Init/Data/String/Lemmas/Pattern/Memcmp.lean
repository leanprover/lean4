/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

prelude
public import Init.Data.String.Pattern.Memcmp
public import Init.Data.ByteArray.Lex
import all Init.Data.String.Pattern.Memcmp
import Init.Data.ByteArray.Lemmas
import Init.Data.Nat.MinMax
import Init.Data.String.OrderInstances

public section

namespace String.Slice.Pattern.Internal

theorem memcmpStrCompare_eq_compare {lhs rhs : String} {lstart rstart len : String.Pos.Raw}
    {h₁ h₂} : memcmpStrCompare lhs rhs lstart rstart len h₁ h₂ =
      compare (lhs.toByteArray.extract lstart.byteIdx (len.offsetBy lstart).byteIdx)
        (rhs.toByteArray.extract rstart.byteIdx (len.offsetBy rstart).byteIdx) := by
  suffices ∀ (curr : String.Pos.Raw),
      memcmpStrCompare.go lhs rhs lstart rstart len h₁ h₂ curr =
      compare (lhs.toByteArray.extract (curr.offsetBy lstart).byteIdx (len.offsetBy lstart).byteIdx)
        (rhs.toByteArray.extract (curr.offsetBy rstart).byteIdx (len.offsetBy rstart).byteIdx) by
    simp [memcmpStrCompare, this]
  intro curr
  simp only [Pos.Raw.le_iff, String.byteIdx_rawEndPos, Pos.Raw.byteIdx_offsetBy] at h₁ h₂
  fun_induction memcmpStrCompare.go with
  | case1 p h₃ h₄ h₅ ih =>
    rw [Pos.Raw.lt_iff] at h₃
    simp only [ih, getUTF8Byte_eq_getElem, Pos.Raw.byteIdx_offsetBy, Pos.Raw.byteIdx_inc]
    rw [ByteArray.compare_extract_extract_of_lt (i := lstart.byteIdx + p.byteIdx) (by omega)
      (by simp; omega) (by omega) (by simp; omega)]
    simp only [Nat.add_assoc]
  | case2 p hp =>
    rw [Pos.Raw.lt_iff] at hp
    rw [ByteArray.extract_eq_empty_iff.2, ByteArray.extract_eq_empty_iff.2, Std.compare_self]
    all_goals simp; omega

theorem memcmpStr_eq_true_iff {lhs rhs : String} {lstart rstart len : String.Pos.Raw}
    {h₁ h₂} : memcmpStr lhs rhs lstart rstart len h₁ h₂ = true ↔
      lhs.toByteArray.extract lstart.byteIdx (len.offsetBy lstart).byteIdx =
        rhs.toByteArray.extract rstart.byteIdx (len.offsetBy rstart).byteIdx := by
  rw [memcmpStr, beq_iff_eq, memcmpStrCompare_eq_compare, Std.compare_eq_eq_iff_eq]

theorem memcmpStrLt_eq_true_iff {lhs rhs : String} {lstart rstart len : String.Pos.Raw}
    {h₁ h₂} : memcmpStrLt lhs rhs lstart rstart len h₁ h₂ = true ↔
      lhs.toByteArray.extract lstart.byteIdx (len.offsetBy lstart).byteIdx <
        rhs.toByteArray.extract rstart.byteIdx (len.offsetBy rstart).byteIdx := by
  rw [memcmpStrLt, beq_iff_eq, memcmpStrCompare_eq_compare, Std.compare_eq_lt]

theorem memcmpSlice_eq_true_iff {lhs rhs : Slice} {lstart rstart len : String.Pos.Raw} {h₁ h₂} :
    memcmpSlice lhs rhs lstart rstart len h₁ h₂ = true ↔
      lhs.copy.toByteArray.extract lstart.byteIdx (len.offsetBy lstart).byteIdx =
        rhs.copy.toByteArray.extract rstart.byteIdx (len.offsetBy rstart).byteIdx := by
  rw [memcmpSlice, memcmpStr_eq_true_iff, toByteArray_copy, toByteArray_copy,
    ByteArray.extract_extract, ByteArray.extract_extract]
  simp only [Pos.Raw.byteIdx_offsetBy, Nat.add_assoc]
  have h₃ := lhs.startInclusive_le_endExclusive
  have h₄ := rhs.startInclusive_le_endExclusive
  simp only [Pos.Raw.le_iff, Pos.Raw.byteIdx_offsetBy, byteIdx_rawEndPos, utf8ByteSize_eq,
    String.Pos.le_iff] at h₁ h₂ h₃ h₄
  rw [Nat.min_eq_left (by omega), Nat.min_eq_left (by omega)]

end String.Slice.Pattern.Internal
