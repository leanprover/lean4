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
import Init.Data.String.Lemmas.Order
import Init.Data.String.Grind

public section

namespace String.Slice

/--
A region or slice of a slice.
-/
@[ext]
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

@[simp]
theorem startInclusive_subslice {s : Slice} {newStart newEnd : s.Pos} {h} :
    (s.subslice newStart newEnd h).startInclusive = newStart := (rfl)

@[simp]
theorem endExclusive_subslice {s : Slice} {newStart newEnd : s.Pos} {h} :
    (s.subslice newStart newEnd h).endExclusive = newEnd := (rfl)

@[inline]
def subslice! (s : Slice) (newStart newEnd : s.Pos) : s.Subslice :=
  if h : newStart ≤ newEnd then s.subslice _ _ h else panic! "Trying to construct a degenerate subslice"

/-- Constructs a subslice of `s` starting at the given position and going until the end of the slice. -/
@[inline]
def subsliceFrom (s : Slice) (newStart : s.Pos) : s.Subslice :=
  s.subslice newStart s.endPos (Slice.Pos.le_endPos _)

@[simp]
theorem startInclusive_subsliceFrom {s : Slice} {newStart : s.Pos} :
    (s.subsliceFrom newStart).startInclusive = newStart := (rfl)

@[simp]
theorem endExclusive_subsliceFrom {s : Slice} {newStart : s.Pos} :
    (s.subsliceFrom newStart).endExclusive = s.endPos := (rfl)

/-- The entire slice, as a subslice of itself. -/
@[inline]
def toSubslice (s : Slice) : s.Subslice :=
  s.subslice s.startPos s.endPos (Slice.Pos.le_endPos _)

namespace Subslice

def ofSliceFrom {s : Slice} {p : s.Pos} (sl : (s.sliceFrom p).Subslice) : s.Subslice where
  startInclusive := Slice.Pos.ofSliceFrom sl.startInclusive
  endExclusive := Slice.Pos.ofSliceFrom sl.endExclusive
  startInclusive_le_endExclusive := Slice.Pos.ofSliceFrom_le_ofSliceFrom_iff.2 sl.startInclusive_le_endExclusive

@[simp]
theorem startInclusive_ofSliceFrom {s : Slice} {p : s.Pos} {sl : (s.sliceFrom p).Subslice} :
    sl.ofSliceFrom.startInclusive = Slice.Pos.ofSliceFrom sl.startInclusive := (rfl)

@[simp]
theorem endExclusive_ofSliceFrom {s : Slice} {p : s.Pos} {sl : (s.sliceFrom p).Subslice} :
    sl.ofSliceFrom.endExclusive = Slice.Pos.ofSliceFrom sl.endExclusive := (rfl)

@[simp]

def extendLeft {s : Slice} {sl : s.Subslice} (newStart : s.Pos) (h : newStart ≤ sl.startInclusive) : s.Subslice where
  startInclusive := newStart
  endExclusive := sl.endExclusive
  startInclusive_le_endExclusive := Std.le_trans h sl.startInclusive_le_endExclusive

@[simp]
theorem startInclusive_extendLeft {s : Slice} {sl : s.Subslice} {newStart : s.Pos} {h} :
    (sl.extendLeft newStart h).startInclusive = newStart := (rfl)

@[simp]
theorem endExclusive_extendLeft {s : Slice} {sl : s.Subslice} {newStart : s.Pos} {h} :
    (sl.extendLeft newStart h).endExclusive = sl.endExclusive := (rfl)

def cast {s t : Slice} (h : s = t) (sl : s.Subslice) : t.Subslice where
  startInclusive := sl.startInclusive.cast h
  endExclusive := sl.endExclusive.cast h
  startInclusive_le_endExclusive := by simpa using sl.startInclusive_le_endExclusive

@[simp]
theorem startInclusive_cast {s t : Slice} {h : s = t} {sl : s.Subslice} :
    (sl.cast h).startInclusive = sl.startInclusive.cast h := (rfl)

@[simp]
theorem endExclusive_cast {s t : Slice} {h : s = t} {sl : s.Subslice} :
    (sl.cast h).endExclusive = sl.endExclusive.cast h := (rfl)

@[simp]
theorem cast_rfl {s : Slice} : Subslice.cast (s := s) rfl = id := by
  ext <;> simp

end Subslice

end String.Slice
