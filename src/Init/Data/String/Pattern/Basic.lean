/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Init.Data.String.Basic
public import Init.Data.Iterators.Basic

set_option doc.verso true

/-!
This module defines the notion of patterns which is central to the {name}`String.Slice` and
{name}`String` API. All functions on {name}`String.Slice` and {name}`String` that
“search for something” are polymorphic over a pattern instead of taking just one particular kind
of pattern such as a {name}`Char`. The key components are:
- {name (scope := "Init.Data.String.Pattern.Basic")}`ToForwardSearcher`
- {name (scope := "Init.Data.String.Pattern.Basic")}`ForwardPattern`
- {name (scope := "Init.Data.String.Pattern.Basic")}`ToBackwardSearcher`
- {name (scope := "Init.Data.String.Pattern.Basic")}`BackwardPattern`
-/

public section

namespace String.Slice.Pattern

/--
A step taken during the traversal of a {name}`Slice` by a forward or backward searcher.
-/
inductive SearchStep (s : Slice) where
  /--
  The subslice starting at {name}`startPos` and ending at {name}`endPos` did not match the pattern.
  -/
  | rejected (startPos endPos : s.Pos)
  /--
  The subslice starting at {name}`startPos` and ending at {name}`endPos` matches the pattern.
  -/
  | matched (startPos endPos : s.Pos)
deriving Inhabited, BEq

/--
Provides a conversion from a pattern to an iterator of {name}`SearchStep` that searches for matches
of the pattern from the start towards the end of a {name}`Slice`.
-/
class ToForwardSearcher {ρ : Type} (pat : ρ) (σ : outParam (Slice → Type)) where
  /--
  Builds an iterator of {name}`SearchStep` corresponding to matches of {name}`pat` along the slice
  {name}`s`. The {name}`SearchStep`s returned by this iterator must contain ranges that are
  adjacent, non-overlapping and cover all of {name}`s`.
  -/
  toSearcher : (s : Slice) → Std.Iter (α := σ s) (SearchStep s)

/--
Provides simple pattern matching capabilities from the start of a {name}`Slice`.

While these operations can be implemented on top of {name}`ToForwardSearcher` some patterns allow
for more efficient implementations. This class can be used to specialize for them. If there is no
need to specialize in this fashion, then
{name (scope := "Init.Data.String.Pattern.Basic")}`ForwardPattern.defaultImplementation` can be used
to automatically derive an instance.
-/
class ForwardPattern {ρ : Type} (pat : ρ) where
  /--
  Checks whether the slice starts with the pattern.
  -/
  startsWith : Slice → Bool
  /--
  Checks whether the slice starts with the pattern. If it does, the slice is returned with the
  prefix removed; otherwise the result is {name}`none`.
  -/
  dropPrefix? : (s : Slice) → Option s.Pos

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
      simp [String.Pos.le_iff, Pos.Raw.le_iff, Slice.utf8ByteSize_eq] at *
      omega)
    (by
      have := rhs.startInclusive_le_endExclusive
      have := rhs.endExclusive.isValid.le_utf8ByteSize
      simp [String.Pos.le_iff, Pos.Raw.le_iff, Slice.utf8ByteSize_eq] at *
      omega)

end Internal

namespace ForwardPattern

variable {ρ : Type} {σ : Slice → Type}
variable [∀ s, Std.Iterator (σ s) Id (SearchStep s)]
variable (pat : ρ) [ToForwardSearcher pat σ]

@[specialize pat]
def defaultStartsWith (s : Slice) : Bool :=
  let searcher := ToForwardSearcher.toSearcher pat s
  match searcher.step with
  | .yield _ (.matched start ..) _ => s.startPos = start
  | _ => false

@[specialize pat]
def defaultDropPrefix? (s : Slice) : Option s.Pos :=
  let searcher := ToForwardSearcher.toSearcher pat s
  match searcher.step with
  | .yield _ (.matched _ endPos) _ => some endPos
  | _ => none

@[always_inline, inline]
def defaultImplementation {pat : ρ} [ToForwardSearcher pat σ] : ForwardPattern pat where
  startsWith := defaultStartsWith pat
  dropPrefix? := defaultDropPrefix? pat

end ForwardPattern

/--
Provides a conversion from a pattern to an iterator of {name}`SearchStep` searching for matches of
the pattern from the end towards the start of a {name}`Slice`.
-/
class ToBackwardSearcher {ρ : Type} (pat : ρ) (σ : outParam (Slice → Type)) where
  /--
  Build an iterator of {name}`SearchStep` corresponding to matches of {lean}`pat` along the slice
  {name}`s`. The {name}`SearchStep`s returned by this iterator must contain ranges that are
  adjacent, non-overlapping and cover all of {name}`s`.
  -/
  toSearcher : (s : Slice) → Std.Iter (α := σ s) (SearchStep s)

/--
Provides simple pattern matching capabilities from the end of a {name}`Slice`.

While these operations can be implemented on top of {name}`ToBackwardSearcher`, some patterns allow
for more efficient implementations. This class can be used to specialize for them. If there is no
need to specialize in this fashion, then
{name (scope := "Init.Data.String.Pattern.Basic")}`BackwardPattern.defaultImplementation` can be
used to automatically derive an instance.
-/
class BackwardPattern {ρ : Type} (pat : ρ) where
  /--
  Checks whether the slice ends with the pattern.
  -/
  endsWith : Slice → Bool
  /--
  Checks whether the slice ends with the pattern. If it does, the slice is returned with the
  suffix removed; otherwise the result is {name}`none`.
  -/
  dropSuffix? : (s : Slice) → Option s.Pos

namespace ToBackwardSearcher

variable {ρ : Type} {σ : Slice → Type}
variable [∀ s, Std.Iterator (σ s) Id (SearchStep s)]
variable (pat : ρ) [ToBackwardSearcher pat σ]

@[specialize pat]
def defaultEndsWith (s : Slice) : Bool :=
  let searcher := ToBackwardSearcher.toSearcher pat s
  match searcher.step with
  | .yield _ (.matched _ endPos) _ => s.endPos = endPos
  | _ => false

@[specialize pat]
def defaultDropSuffix? (s : Slice) : Option s.Pos :=
  let searcher := ToBackwardSearcher.toSearcher pat s
  match searcher.step with
  | .yield _ (.matched startPos _) _ => some startPos
  | _ => none

@[always_inline, inline]
def defaultImplementation {pat : ρ} [ToBackwardSearcher pat σ] : BackwardPattern pat where
  endsWith := defaultEndsWith pat
  dropSuffix? := defaultDropSuffix? pat

end ToBackwardSearcher

end String.Slice.Pattern
