/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

prelude
public import Init.Data.String.Basic
import Init.Omega
import Init.Data.String.OrderInstances
import Init.Data.String.Lemmas.Basic

set_option doc.verso true

/-!
# Finding positions in a string relative to a given raw position
-/

public section

namespace String

/--
Obtains the smallest valid position that is greater than or equal to the given byte position.
-/
def Slice.posGE (s : Slice) (offset : String.Pos.Raw) (h : offset ≤ s.rawEndPos) : s.Pos :=
  if h' : offset.IsValidForSlice s then
    s.pos offset h'
  else
    have : offset < s.rawEndPos := Std.not_le.1 (fun h₁ => h' (Std.le_antisymm h h₁ ▸ Pos.Raw.isValidForSlice_rawEndPos))
    s.posGE offset.inc (by simpa)
termination_by s.utf8ByteSize - offset.byteIdx
decreasing_by
  simp only [Pos.Raw.lt_iff, byteIdx_rawEndPos, Pos.Raw.byteIdx_inc] at this ⊢
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

/--
Obtains the largest valid position that is less than or equal to the given byte position.
-/
def Slice.posLE (s : Slice) (offset : String.Pos.Raw) : s.Pos :=
  if h' : offset.IsValidForSlice s then
    s.pos offset h'
  else
    have : offset ≠ 0 := by rintro rfl; simp at h'
    s.posLE offset.dec
termination_by offset.byteIdx
decreasing_by simp only [ne_eq, Pos.Raw.eq_zero_iff, Pos.Raw.byteIdx_dec] at ⊢ this; omega

/--
Obtains the largest valid position that is strictly less than the given byte position.
-/
@[inline]
def Slice.posLT (s : Slice) (offset : String.Pos.Raw) (_h : 0 < offset) : s.Pos :=
  s.posLE offset.dec

/--
Obtains the largest valid position that is less than or equal to the given byte position.
-/
@[inline]
def posLE (s : String) (offset : String.Pos.Raw) : s.Pos :=
  Pos.ofToSlice (s.toSlice.posLE offset)

/--
Obtains the largest valid position that is strictly less than the given byte position.
-/
@[inline]
def posLT (s : String) (offset : String.Pos.Raw) (h : 0 < offset) : s.Pos :=
  Pos.ofToSlice (s.toSlice.posLT offset h)

/--
Returns the previous valid position before the given position, given a proof that the position
is not the start position, which guarantees that such a position exists.
-/
@[inline]
def Slice.Pos.prev {s : Slice} (pos : s.Pos) (h : pos ≠ s.startPos) : s.Pos :=
  s.posLT pos.offset (by simpa [Pos.Raw.pos_iff_ne_zero, Pos.ext_iff] using h)

/-- Returns the previous valid position before the given position, or {lean}`none` if the position is
the start position. -/
@[expose]
def Slice.Pos.prev? {s : Slice} (pos : s.Pos) : Option s.Pos :=
  if h : pos = s.startPos then none else some (pos.prev h)

/-- Returns the previous valid position before the given position, or panics if the position is
the start position. -/
@[expose]
def Slice.Pos.prev! {s : Slice} (pos : s.Pos) : s.Pos :=
  if h : pos = s.startPos then panic! "The start position has no previous position" else pos.prev h

/-- Returns the previous valid position before the given position, given a proof that the position
is not the start position, which guarantees that such a position exists. -/
@[inline, expose]
def Pos.prev {s : String} (pos : s.Pos) (h : pos ≠ s.startPos) : s.Pos :=
  ofToSlice (pos.toSlice.prev (ne_of_apply_ne Pos.ofToSlice (by simpa)))

/-- Returns the previous valid position before the given position, or {lean}`none` if the position is
the start position. -/
@[inline, expose]
def Pos.prev? {s : String} (pos : s.Pos) : Option s.Pos :=
  pos.toSlice.prev?.map Pos.ofToSlice

/-- Returns the previous valid position before the given position, or panics if the position is
the start position. -/
@[inline, expose]
def Pos.prev! {s : String} (pos : s.Pos) : s.Pos :=
  ofToSlice pos.toSlice.prev!

/--
Iterates {lean}`p.prev` {name}`n` times.

If this would move {name}`p` past the start of {name}`s`, the result is {lean}`s.endPos`.
-/
def Slice.Pos.prevn {s : Slice} (p : s.Pos) (n : Nat) : s.Pos :=
  match n with
  | 0 => p
  | n + 1 =>
    if h : p ≠ s.startPos then
      prevn (p.prev h) n
    else
      p

/--
Iterates {lean}`p.prev` {name}`n` times.

If this would move {name}`p` past the start of {name}`s`, the result is {lean}`s.startPos`.
-/
@[inline]
def Pos.prevn {s : String} (p : s.Pos) (n : Nat) : s.Pos :=
  ofToSlice (p.toSlice.prevn n)

end String
