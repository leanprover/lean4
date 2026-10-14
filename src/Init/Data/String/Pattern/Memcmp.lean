/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Init.Data.String.Basic
import Init.Data.String.Lemmas.Order
import Init.Omega

public section

namespace String.Slice.Pattern

namespace Internal

@[extern "lean_string_memcmp"]
def memcmpStr (lhs rhs : @& String) (lstart : @& String.Pos.Raw) (rstart : @& String.Pos.Raw)
    (len : @& String.Pos.Raw) (h1 : len.offsetBy lstart ≤ lhs.rawEndPos)
    (h2 : len.offsetBy rstart ≤ rhs.rawEndPos) : Bool :=
  go 0
where
  go (curr : String.Pos.Raw) : Bool :=
    if h : curr < len then
      have hl := by
        simp [Pos.Raw.le_iff, Pos.Raw.lt_iff] at h h1 ⊢
        omega
      have hr := by
        simp [Pos.Raw.le_iff, Pos.Raw.lt_iff] at h h2 ⊢
        omega
      if lhs.getUTF8Byte (curr.offsetBy lstart) hl == rhs.getUTF8Byte (curr.offsetBy rstart) hr then
        go curr.inc
      else
        false
    else
      true
  termination_by len.byteIdx - curr.byteIdx
  decreasing_by
    simp [Pos.Raw.lt_iff] at h ⊢
    omega

@[inline]
def memcmpSlice (lhs rhs : Slice) (lstart : String.Pos.Raw) (rstart : String.Pos.Raw)
    (len : String.Pos.Raw) (h1 : len.offsetBy lstart ≤ lhs.rawEndPos)
    (h2 : len.offsetBy rstart ≤ rhs.rawEndPos) : Bool :=
  memcmpStr
    lhs.str
    rhs.str
    (lstart.offsetBy lhs.startInclusive.offset)
    (rstart.offsetBy rhs.startInclusive.offset)
    len
    (by
      have := lhs.startInclusive_le_endExclusive
      have := lhs.endExclusive.isValid.le_utf8ByteSize
      simp [String.Pos.le_iff, Pos.Raw.le_iff, Slice.utf8ByteSize_eq,
        -String.Pos.byteIdx_offset_le_utf8ByteSize] at *
      omega)
    (by
      have := rhs.startInclusive_le_endExclusive
      have := rhs.endExclusive.isValid.le_utf8ByteSize
      simp [String.Pos.le_iff, Pos.Raw.le_iff, Slice.utf8ByteSize_eq,
        -String.Pos.byteIdx_offset_le_utf8ByteSize] at *
      omega)

end Internal

end String.Slice.Pattern
