/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, hatzka
-/
module

prelude
public import Init.Data.String.Slice
import all Init.Data.String.Slice
import Init.Data.String.Lemmas.Pattern.Memcmp
import Init.Data.String.Lemmas.Basic
import Init.Data.ByteArray.Lemmas
import Init.Data.Option.Lemmas

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

section ForwardPatternUsers

variable {s : Slice} {ρ : Type} {pat : ρ} [Pattern.ForwardPattern pat]

@[simp]
theorem dropPrefix?_str {isSome : (s.dropPrefix? pat).isSome} :
  ((s.dropPrefix? pat).get isSome).str = s.str
:= by
  unfold dropPrefix?
  simp

@[simp]
theorem dropPrefix_str : (s.dropPrefix pat).str = s.str := by
  unfold dropPrefix
  match h : s.dropPrefix? pat with
  | none => simp
  | some s' =>
    have := Option.isSome_of_eq_some h
    rw [← h, ← Option.get_eq_getD (h := this)]
    apply dropPrefix?_str

@[simp]
theorem drop_str {n : Nat} : (s.drop n).str = s.str := by rfl

@[simp]
theorem dropWhile_str : (s.dropWhile pat).str = s.str := by
  unfold dropWhile
  apply go
where
  go {curr : s.Pos} : (dropWhile.go s pat curr).str = s.str := by
    unfold dropWhile.go
    match Pattern.ForwardPattern.dropPrefix? pat (s.sliceFrom curr) with
    | none => simp
    | some s' =>
      simp
      split
      · apply go
      · simp
  termination_by curr

@[simp]
theorem trimAsciiStart_str : s.trimAsciiStart.str = s.str := by
  unfold trimAsciiStart
  simp

@[simp]
theorem take_str {n : Nat} : (s.take n).str = s.str := by
  unfold take
  simp

@[simp]
theorem takeWhile_str : (s.takeWhile pat).str = s.str := by
  unfold takeWhile
  apply go
where
  go {curr : s.Pos} : (takeWhile.go s pat curr).str = s.str := by
    unfold takeWhile.go
    match Pattern.ForwardPattern.dropPrefix? pat (s.sliceFrom curr) with
    | none => simp
    | some s' =>
      simp
      split
      · apply go
      · simp
  termination_by curr

end ForwardPatternUsers

section BackwardPatternUsers

variable {s : Slice} {ρ : Type} {pat : ρ} [Pattern.BackwardPattern pat]

@[simp]
theorem dropSuffix?_str {isSome : (s.dropSuffix? pat).isSome} :
  ((s.dropSuffix? pat).get isSome).str = s.str
:= by
  unfold dropSuffix?
  simp

@[simp]
theorem dropSuffix_str : (s.dropSuffix pat).str = s.str := by
  unfold dropSuffix
  match h : s.dropSuffix? pat with
  | none => simp
  | some s' =>
    have := Option.isSome_of_eq_some h
    rw [← h, ← Option.get_eq_getD (h := this)]
    apply dropSuffix?_str

@[simp]
theorem dropEnd_str {n : Nat} : (s.dropEnd n).str = s.str := by rfl

@[simp]
theorem dropEndWhile_str : (s.dropEndWhile pat).str = s.str := by
  unfold dropEndWhile
  apply go
where
  go {curr : s.Pos} : (dropEndWhile.go s pat curr).str = s.str := by
    unfold dropEndWhile.go
    match Pattern.BackwardPattern.dropSuffix? pat (s.sliceTo curr) with
    | none => simp
    | some s' =>
      simp
      split
      · apply go
      · simp
  termination_by curr.down

@[simp]
theorem trimAsciiEnd_str : s.trimAsciiEnd.str = s.str := by
  unfold trimAsciiEnd
  simp

@[simp]
theorem takeEnd_str {n : Nat} : (s.takeEnd n).str = s.str := by
  unfold takeEnd
  simp

@[simp]
theorem takeEndWhile_str : (s.takeEndWhile pat).str = s.str := by
  unfold takeEndWhile
  apply go
where
  go {curr : s.Pos} : (takeEndWhile.go s pat curr).str = s.str := by
    unfold takeEndWhile.go
    match Pattern.BackwardPattern.dropSuffix? pat (s.sliceTo curr) with
    | none => simp
    | some s' =>
      simp
      split
      · apply go
      · simp
  termination_by curr.down

end BackwardPatternUsers

@[simp]
theorem trimAscii_str {s : Slice} : s.trimAscii.str = s.str := by
  unfold trimAscii
  simp

end String.Slice
