/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

prelude
public import Init.Data.String.Basic
import Init.Data.String.Termination
import Init.Data.String.Lemmas.Basic

public section

namespace String.Slice

/--
A region or slice of a slice.
-/
structure Subslice (s : Slice) where
  /-- The byte position of the start of the subslice. -/
  startInclusive : s.Pos
  /-- The byte position of the end of the subslice. -/
  endExclusive : s.Pos
  /-- The subslice is not degenerate (but it may be empty). -/
  startInclusive_le_endExclusive : startInclusive ≤ endExclusive

instance {s : Slice} : Inhabited s.Subslice where
  default := ⟨s.endPos, s.endPos, by exact Slice.Pos.le_refl _⟩

namespace Subslice

/-- Turns a subslice into a standalone slice. -/
@[inline, expose] -- for the defeq `sl.toSlice.str = s.str`.
def toSlice {s : Slice} (sl : s.Subslice) : Slice :=
  s.slice sl.startInclusive sl.endExclusive sl.startInclusive_le_endExclusive

@[simp]
theorem str_toSlice {s : Slice} {sl : s.Subslice} : sl.toSlice.str = s.str := rfl

@[simp]
theorem startInclusive_toSlice {s : Slice} {sl : s.Subslice} :
    sl.toSlice.startInclusive = sl.startInclusive.str := rfl

@[simp]
theorem endExclusive_toSlice {s : Slice} {sl : s.Subslice} :
    sl.toSlice.endExclusive = sl.endExclusive.str := rfl

end Subslice

/-- Constructs a subslice of `s`. -/
@[inline]
def subslice (s : Slice) (newStart newEnd : s.Pos) (h : newStart ≤ newEnd) : s.Subslice where
  startInclusive := newStart
  endExclusive := newEnd
  startInclusive_le_endExclusive := h

@[simp]
theorem toSlice_subslice {s : Slice} {newStart newEnd h} :
    (s.subslice newStart newEnd h).toSlice = s.slice newStart newEnd h := (rfl)

@[inline]
def subslice! (s : Slice) (newStart newEnd : s.Pos) : s.Subslice :=
  if h : newStart ≤ newEnd then s.subslice _ _ h else panic! "Trying to construct a degenerate subslice"

/-- Constructs a subslice of `s` starting at the given position and going until the end of the slice. -/
@[inline]
def subsliceFrom (s : Slice) (newStart : s.Pos) : s.Subslice :=
  s.subslice newStart s.endPos (Slice.Pos.le_endPos _)

/-- The entire slice, as a subslice of itself. -/
@[inline]
def toSubslice (s : Slice) : s.Subslice :=
  s.subslice s.startPos s.endPos (Slice.Pos.le_endPos _)

end String.Slice
