/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

prelude
public import Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.Basic
import Init.Data.ByteArray.Lemmas
import Init.ByCases
import Init.Data.Nat.MinMax

public section

namespace String.Slice.Pattern.Internal

theorem memcmpStr_eq_true_iff {lhs rhs : String} {lstart rstart len : String.Pos.Raw}
    {h₁ h₂} : memcmpStr lhs rhs lstart rstart len h₁ h₂ = true ↔
      lhs.toByteArray.extract lstart.byteIdx (len.offsetBy lstart).byteIdx =
        rhs.toByteArray.extract rstart.byteIdx (len.offsetBy rstart).byteIdx := by
  suffices ∀ (curr : String.Pos.Raw),
      memcmpStr.go lhs rhs lstart rstart len h₁ h₂ curr = true ↔
      lhs.toByteArray.extract (curr.offsetBy lstart).byteIdx (len.offsetBy lstart).byteIdx =
      rhs.toByteArray.extract (curr.offsetBy rstart).byteIdx (len.offsetBy rstart).byteIdx by
    simp [memcmpStr, this]
  intro curr
  simp [Pos.Raw.le_iff] at h₁ h₂
  by_cases hc : len.byteIdx < curr.byteIdx
  · rw [ByteArray.extract_eq_empty_iff.2, ByteArray.extract_eq_empty_iff.2, memcmpStr.go,
      dif_neg (Std.not_lt.2 (Std.le_of_lt (Pos.Raw.lt_iff.2 hc)))]
    simp only
    all_goals simp; omega
  · simp only [Pos.Raw.byteIdx_offsetBy]
    rw [(by omega : len.byteIdx = curr.byteIdx + (len.byteIdx - curr.byteIdx)),
      ← Nat.add_assoc, ← Nat.add_assoc,
      ByteArray.extract_eq_extract_iff_getElem (by simp; omega) (by simp; omega)]
    fun_induction memcmpStr.go with
    | case1 p h₃ h₄ h₅ h ih =>
      rw [Pos.Raw.lt_iff] at h₃
      rw [ih (by simp; omega)]
      simp only [String.getUTF8Byte, Pos.Raw.byteIdx_offsetBy, beq_iff_eq] at h
      simp only [Pos.Raw.byteIdx_inc, Nat.add_assoc, Nat.add_comm 1]
      refine ⟨fun h k hk => ?_, fun h k hk => h (k + 1) (by omega)⟩
      match k with
      | 0 => simpa
      | k + 1 => exact h k (by omega)
    | case2 p h₃ h₄ h₅ h => simpa using ⟨0, by rw [Pos.Raw.lt_iff] at h₃; omega, by simpa using h⟩
    | case3 p hp => simp [(by rw [Pos.Raw.lt_iff] at hp; omega : len.byteIdx = p.byteIdx)]

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
