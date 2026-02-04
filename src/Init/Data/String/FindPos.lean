/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

prelude
public import Init.Data.String.Basic
import Init.Data.Int.Lemmas
import Init.Data.Int.Order
import Init.Omega

set_option doc.verso true

/-!
# Finding positions in a string relative to a given raw position
-/

public section

namespace String

/--
Obtains the smallest valid position that is greater than or equal to the given byte position.
-/
def Slice.posGE (s : Slice) (offset : String.Pos.Raw)  (_h : offset ≤ s.rawEndPos) : s.Pos :=
  if h : offset < s.rawEndPos then
    if h' : (s.getUTF8Byte offset h).IsUTF8FirstByte then
      s.pos offset (Pos.Raw.isValidForSlice_iff_isUTF8FirstByte.2 (Or.inr ⟨_, h'⟩))
    else
      s.posGE offset.inc (by simpa)
  else
    s.endPos
termination_by s.utf8ByteSize - offset.byteIdx
decreasing_by
  simp only [Pos.Raw.lt_iff, byteIdx_rawEndPos, utf8ByteSize_eq, Pos.Raw.byteIdx_inc] at h ⊢
  omega

/--
Obtains the smallest valid position that is strictly greater than the given byte position.
-/
@[inline]
def Slice.posGT (s : Slice) (offset : String.Pos.Raw)  (h : offset < s.rawEndPos) : s.Pos :=
  s.posGE offset.inc (by simpa)

@[deprecated Slice.posGT (since := "2026-02-03")]
def Slice.findNextPos (offset : String.Pos.Raw) (s : Slice) (h : offset < s.rawEndPos) : s.Pos :=
  s.posGT offset h

/--
Obtains the smallest valid position that is greater than or equal to the given byte position.
-/
@[inline]
def posGE (s : String) (offset : String.Pos.Raw) (h : offset ≤ s.rawEndPos) : s.Pos :=
  Pos.ofToSlice (s.toSlice.posGE offset (by simpa))

/--
Obtains the smallest valid position that is strictly greater than the given byte position.
-/
@[inline]
def posGT (s : String) (offset : String.Pos.Raw) (h : offset < s.rawEndPos) : s.Pos :=
  Pos.ofToSlice (s.toSlice.posGT offset (by simpa))

end String
