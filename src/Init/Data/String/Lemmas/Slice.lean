/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

prelude
public import Init.Data.String.Slice
import all Init.Data.String.Slice
import Init.Data.String.Lemmas.Pattern.Memcmp
import Init.Data.String.Lemmas.Basic
import Init.Data.ByteArray.Lemmas

public section

namespace String.Slice

section BEq

@[simp]
theorem beq_eq_true_iff {s t : Slice} : s == t ↔ s.copy = t.copy := by
  simp only [BEq.beq, beq]
  split <;> rename_i h
  · rw [Pattern.Internal.memcmpSlice_eq_true_iff]
    simp only [offset_startPos, Pos.Raw.byteIdx_zero, Pos.Raw.offsetBy_zero, byteIdx_rawEndPos]
    rw (occs := [2]) [h]
    rw [utf8ByteSize_eq_size_toByteArray_copy, ByteArray.extract_zero_size,
      utf8ByteSize_eq_size_toByteArray_copy, ByteArray.extract_zero_size, String.toByteArray_inj]
  · simpa using ne_of_apply_ne String.utf8ByteSize (by simpa)

@[simp]
theorem beq_eq_false_iff {s t : Slice} : (s == t) = false ↔ s.copy ≠ t.copy := by
  simp [← Bool.not_eq_true]

theorem beq_eq_decide {s t : Slice} : (s == t) = decide (s.copy = t.copy) := by
  cases h : s == t <;> simp_all

end BEq

end String.Slice
