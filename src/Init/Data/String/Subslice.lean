/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

prelude
public import Init.Data.String.Basic

set_option doc.verso true

public section

namespace String.Slice

/--
A region or slice of a fixed slice.

Given a {name}`Slice` {name}`s`, the type {lean}`s.Subslice` is the type of half-open regions
in {name}`s` delineated by a valid position on both sides.

This type is useful to track regions of interest within some larger slice that is also of interest.
In contrast, {name}`Slice` is used to track regions of interest whithin some larger string that is
not or no longer relevant.

Equality on {name}`Subslice` is somewhat better behaved than on {name}`Slice`, but note that there
will in general be many different representations of the empty subslice of a slice.
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

/--
Turns a subslice into a standalone slice by "forgetting" which slice the subslice is a sublice of.
-/
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

instance {s : Slice} : CoeOut s.Subslice Slice where
  coe := Subslice.toSlice

/--
Creates a {name}`String` from a {name}`Subslice` by copying out the bytes.
-/
@[inline]
def copy {s : Slice} (sl : s.Subslice) : String :=
  sl.toSlice.copy

@[inline, inherit_doc copy]
def toString {s : Slice} (sl : s.Subslice) : String :=
  sl.copy

instance {s : Slice} : ToString s.Subslice where
  toString

end Subslice

/--
Constructs a subslice of {name}`s` given the bounds of the subslice and a proof that the subslice
is non-degenerate.
-/
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

/--
Constructs a subslice of {name}`s` given the bounds of the subslice. If the subslice would be
degenerate, this function panics.
-/
def subslice! (s : Slice) (newStart newEnd : s.Pos) : s.Subslice :=
  if h : newStart ≤ newEnd then
    s.subslice _ _ h
  else
    panic! "Trying to construct a degenerate subslice"

theorem subslice!_eq_subslice {s : Slice} {newStart newEnd : s.Pos} (h) :
    s.subslice! newStart newEnd = s.subslice newStart newEnd h := by
  simp [subslice!, h]

/--
Constructs a subslice of {name}`s` starting at the given position and going until the end of the
slice.
-/
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

@[simp]
theorem startInclusive_toSubslice {s : Slice} : s.toSubslice.startInclusive = s.startPos := by
  simp [toSubslice]

@[simp]
theorem endExclusive_toSubslice {s : Slice} : s.toSubslice.endExclusive = s.endPos := by
  simp [toSubslice]

namespace Subslice

/--
Given a position {name}`p` within a slice {name}`s` and a subslice {name}`sl` of
{lean}`s.sliceFrom p`, reinterpret {name}`sl` as a subslice of {name}`s` by applying
{name}`Pos.ofSliceFrom` to the endpoints.
-/
@[inline]
def ofSliceFrom {s : Slice} {p : s.Pos} (sl : (s.sliceFrom p).Subslice) : s.Subslice where
  startInclusive := Slice.Pos.ofSliceFrom sl.startInclusive
  endExclusive := Slice.Pos.ofSliceFrom sl.endExclusive
  startInclusive_le_endExclusive :=
    Slice.Pos.ofSliceFrom_le_ofSliceFrom_iff.2 sl.startInclusive_le_endExclusive

@[simp]
theorem startInclusive_ofSliceFrom {s : Slice} {p : s.Pos} {sl : (s.sliceFrom p).Subslice} :
    sl.ofSliceFrom.startInclusive = Slice.Pos.ofSliceFrom sl.startInclusive := (rfl)

@[simp]
theorem endExclusive_ofSliceFrom {s : Slice} {p : s.Pos} {sl : (s.sliceFrom p).Subslice} :
    sl.ofSliceFrom.endExclusive = Slice.Pos.ofSliceFrom sl.endExclusive := (rfl)

/--
Given a subslice {name}`sl` of {name}`s` and a position {name}`newStart` that is at most the
start position of the subslice, obtain a new subslice whose start is {name}`newStart` and whose
end is the end of {name}`sl`.
-/
@[inline]
def extendLeft {s : Slice} (sl : s.Subslice) (newStart : s.Pos)
    (h : newStart ≤ sl.startInclusive) : s.Subslice where
  startInclusive := newStart
  endExclusive := sl.endExclusive
  startInclusive_le_endExclusive := Slice.Pos.le_trans h sl.startInclusive_le_endExclusive

@[simp]
theorem startInclusive_extendLeft {s : Slice} {sl : s.Subslice} {newStart : s.Pos} {h} :
    (sl.extendLeft newStart h).startInclusive = newStart := (rfl)

@[simp]
theorem endExclusive_extendLeft {s : Slice} {sl : s.Subslice} {newStart : s.Pos} {h} :
    (sl.extendLeft newStart h).endExclusive = sl.endExclusive := (rfl)

@[simp]
theorem extendLeft_extendLeft {s : Slice} {sl : s.Subslice} (p₁ p₂) (h₂ h₁) :
    (sl.extendLeft p₂ h₂).extendLeft p₁ h₁ =
      sl.extendLeft p₁ (by exact Pos.le_trans h₁ h₂) := by
  ext <;> simp

@[simp]
theorem extendLeft_self {s : Slice} {sl : s.Subslice} :
    sl.extendLeft sl.startInclusive (by exact Pos.le_refl _) = sl := by
  ext <;> simp

/--
Given a subslice of {name}`s` and a proof that {lean}`s = t`, obtain the corresponding subslice of
{name}`t`.
-/
@[inline]
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
