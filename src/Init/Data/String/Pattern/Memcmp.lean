/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Init.Data.String.Basic
public import Init.Data.Ord.Basic
import Init.Data.Ord.UInt
import Init.Data.String.Lemmas.Order
import Init.Omega

public section

namespace String.Slice.Pattern

namespace Internal

@[extern "lean_string_memcmp_compare"]
def memcmpStrCompare (lhs rhs : @& String) (lstart : @& String.Pos.Raw) (rstart : @& String.Pos.Raw)
    (len : @& Nat) (h1 : lstart.increaseBy len ≤ lhs.rawEndPos)
    (h2 : rstart.increaseBy len ≤ rhs.rawEndPos) : Ordering :=
  go 0
where
  go (curr : Nat) : Ordering :=
    if h : curr < len then
      have hl := by
        simp [Pos.Raw.le_iff, Pos.Raw.lt_iff] at h1 ⊢
        omega
      have hr := by
        simp [Pos.Raw.le_iff, Pos.Raw.lt_iff] at h2 ⊢
        omega
      (compare (lhs.getUTF8Byte (lstart.increaseBy curr) hl)
        (rhs.getUTF8Byte (rstart.increaseBy curr) hr)).then (go (curr + 1))
    else
      .eq
  termination_by len - curr

@[extern "lean_string_memcmp"]
def memcmpStr (lhs rhs : @& String) (lstart : @& String.Pos.Raw) (rstart : @& String.Pos.Raw)
    (len : @& Nat) (h1 : lstart.increaseBy len ≤ lhs.rawEndPos)
    (h2 : rstart.increaseBy len ≤ rhs.rawEndPos) : Bool :=
  memcmpStrCompare lhs rhs lstart rstart len h1 h2 == .eq

@[extern "lean_string_memcmp_lt"]
def memcmpStrLt (lhs rhs : @& String) (lstart : @& String.Pos.Raw) (rstart : @& String.Pos.Raw)
    (len : @& Nat) (h1 : lstart.increaseBy len ≤ lhs.rawEndPos)
    (h2 : rstart.increaseBy len ≤ rhs.rawEndPos) : Bool :=
  memcmpStrCompare lhs rhs lstart rstart len h1 h2 == .lt

theorem offsetBy_increaseBy_le_rawEndPos_str {s : Slice} {p : String.Pos.Raw} {len : Nat}
    (h : p.increaseBy len ≤ s.rawEndPos) :
    (p.offsetBy s.startInclusive.offset).increaseBy len ≤ s.str.rawEndPos := by
  have := s.startInclusive_le_endExclusive
  have := s.endExclusive.isValid.le_utf8ByteSize
  simp [String.Pos.le_iff, Pos.Raw.le_iff, Slice.utf8ByteSize_eq,
    -String.Pos.byteIdx_offset_le_utf8ByteSize] at *
  omega

@[inline]
def memcmpSliceCompare (lhs rhs : Slice) (lstart : String.Pos.Raw) (rstart : String.Pos.Raw)
    (len : Nat) (h1 : lstart.increaseBy len ≤ lhs.rawEndPos)
    (h2 : rstart.increaseBy len ≤ rhs.rawEndPos) : Ordering :=
  memcmpStrCompare lhs.str rhs.str (lstart.offsetBy lhs.startInclusive.offset)
    (rstart.offsetBy rhs.startInclusive.offset) len (offsetBy_increaseBy_le_rawEndPos_str h1)
    (offsetBy_increaseBy_le_rawEndPos_str h2)

@[inline]
def memcmpSlice (lhs rhs : Slice) (lstart : String.Pos.Raw) (rstart : String.Pos.Raw)
    (len : Nat) (h1 : lstart.increaseBy len ≤ lhs.rawEndPos)
    (h2 : rstart.increaseBy len ≤ rhs.rawEndPos) : Bool :=
  memcmpStr lhs.str rhs.str (lstart.offsetBy lhs.startInclusive.offset)
    (rstart.offsetBy rhs.startInclusive.offset) len (offsetBy_increaseBy_le_rawEndPos_str h1)
    (offsetBy_increaseBy_le_rawEndPos_str h2)

@[inline]
def memcmpSliceLt (lhs rhs : Slice) (lstart : String.Pos.Raw) (rstart : String.Pos.Raw)
    (len : Nat) (h1 : lstart.increaseBy len ≤ lhs.rawEndPos)
    (h2 : rstart.increaseBy len ≤ rhs.rawEndPos) : Bool :=
  memcmpStrLt lhs.str rhs.str (lstart.offsetBy lhs.startInclusive.offset)
    (rstart.offsetBy rhs.startInclusive.offset) len (offsetBy_increaseBy_le_rawEndPos_str h1)
    (offsetBy_increaseBy_le_rawEndPos_str h2)

end Internal

end String.Slice.Pattern
