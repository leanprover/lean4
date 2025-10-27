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
  The subslice starting at {name}`startPos` and ending at {name}`endPos` did not match the pattern.
  -/
  | matched (startPos endPos : s.Pos)
deriving Inhabited, BEq

/--
Provides a conversion from a pattern to an iterator of {name}`SearchStep` that searches for matches
of the pattern from the start towards the end of a {name}`Slice`.
-/
class ToForwardSearcher (ρ : Type) (σ : outParam (Slice → Type)) where
  /--
  Builds an iterator of {name}`SearchStep` corresponding to matches of {name}`pat` along the slice
  {name}`s`. The {name}`SearchStep`s returned by this iterator must contain ranges that are
  adjacent, non-overlapping and cover all of {name}`s`.
  -/
  toSearcher : (s : Slice) → (pat : ρ) → Std.Iter (α := σ s) (SearchStep s)

/--
Provides simple pattern matching capabilities from the start of a {name}`Slice`.

While these operations can be implemented on top of {name}`ToForwardSearcher` some patterns allow
for more efficient implementations. This class can be used to specialize for them. If there is no
need to specialize in this fashion, then
{name (scope := "Init.Data.String.Pattern.Basic")}`ForwardPattern.defaultImplementation` can be used
to automatically derive an instance.
-/
class ForwardPattern (ρ : Type) where
  /--
  Checks whether the slice starts with the pattern.
  -/
  startsWith : Slice → ρ → Bool
  /--
  Checks whether the slice starts with the pattern. If it does, the slice is returned with the
  prefix removed; otherwise the result is {name}`none`.
  -/
  dropPrefix? : (s : Slice) → ρ → Option s.Pos

namespace Internal

@[extern "lean_slice_memcmp"]
def memcmp (lhs rhs : @& Slice) (lstart : @& String.Pos.Raw) (rstart : @& String.Pos.Raw)
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

variable {ρ : Type} {σ : Slice → Type}
variable [∀ s, Std.Iterators.Iterator (σ s) Id (SearchStep s)]
variable [∀ s, Std.Iterators.Finite (σ s) Id]

/--
Tries to skip the {name}`searcher` until the next {name}`SearchStep.matched` and return it. If no
match is found until the end returns {name}`none`.
-/
@[inline]
def nextMatch (searcher : Std.Iter (α := σ s) (SearchStep s)) :
    Option (Std.Iter (α := σ s) (SearchStep s) × s.Pos × s.Pos) :=
  go searcher
where
  go [∀ s, Std.Iterators.Finite (σ s) Id] (searcher : Std.Iter (α := σ s) (SearchStep s)) :
      Option (Std.Iter (α := σ s) (SearchStep s) × s.Pos × s.Pos) :=
    match searcher.step with
    | .yield it (.matched startPos endPos) _ => some (it, startPos, endPos)
    | .yield it (.rejected ..) _ | .skip it .. => go it
    | .done .. => none
  termination_by Std.Iterators.Iter.finitelyManySteps searcher

/--
Tries to skip the {name}`searcher` until the next {name}`SearchStep.rejected` and return it. If no
reject is found until the end returns {name}`none`.
-/
@[inline]
def nextReject (searcher : Std.Iter (α := σ s) (SearchStep s)) :
    Option (Std.Iter (α := σ s) (SearchStep s) × s.Pos × s.Pos) :=
  go searcher
where
  go [∀ s, Std.Iterators.Finite (σ s) Id] (searcher : Std.Iter (α := σ s) (SearchStep s)) :
      Option (Std.Iter (α := σ s) (SearchStep s) × s.Pos × s.Pos) :=
    match searcher.step with
    | .yield it (.rejected startPos endPos) _ => some (it, startPos, endPos)
    | .yield it (.matched ..) _ | .skip it .. => go it
    | .done .. => none
  termination_by Std.Iterators.Iter.finitelyManySteps searcher

end Internal

namespace ForwardPattern

variable {ρ : Type} {σ : Slice → Type}
variable [∀ s, Std.Iterators.Iterator (σ s) Id (SearchStep s)]
variable [ToForwardSearcher ρ σ]

@[specialize pat]
def defaultStartsWith (s : Slice) (pat : ρ) : Bool :=
  let searcher := ToForwardSearcher.toSearcher s pat
  match searcher.step with
  | .yield _ (.matched start ..) _ => s.startPos = start
  | _ => false

@[specialize pat]
def defaultDropPrefix? (s : Slice) (pat : ρ) : Option s.Pos :=
  let searcher := ToForwardSearcher.toSearcher s pat
  match searcher.step with
  | .yield _ (.matched _ endPos) _ => some endPos
  | _ => none

@[always_inline, inline]
def defaultImplementation : ForwardPattern ρ where
  startsWith := defaultStartsWith
  dropPrefix? := defaultDropPrefix?

end ForwardPattern

/--
Provides a conversion from a pattern to an iterator of {name}`SearchStep` searching for matches of
the pattern from the end towards the start of a {name}`Slice`.
-/
class ToBackwardSearcher (ρ : Type) (σ : outParam (Slice → Type)) where
  /--
  Build an iterator of {name}`SearchStep` corresponding to matches of {lean}`pat` along the slice
  {name}`s`. The {name}`SearchStep`s returned by this iterator must contain ranges that are
  adjacent, non-overlapping and cover all of {name}`s`.
  -/
  toSearcher : (s : Slice) → (pat : ρ) → Std.Iter (α := σ s) (SearchStep s)

/--
Provides simple pattern matching capabilities from the end of a {name}`Slice`.

While these operations can be implemented on top of {name}`ToBackwardSearcher`, some patterns allow
for more efficient implementations. This class can be used to specialize for them. If there is no
need to specialize in this fashion, then
{name (scope := "Init.Data.String.Pattern.Basic")}`BackwardPattern.defaultImplementation` can be
used to automatically derive an instance.
-/
class BackwardPattern (ρ : Type) where
  /--
  Checks whether the slice ends with the pattern.
  -/
  endsWith : Slice → ρ → Bool
  /--
  Checks whether the slice ends with the pattern. If it does, the slice is returned with the
  suffix removed; otherwise the result is {name}`none`.
  -/
  dropSuffix? : (s : Slice) → ρ → Option s.Pos

namespace ToBackwardSearcher

variable {ρ : Type} {σ : Slice → Type}
variable [∀ s, Std.Iterators.Iterator (σ s) Id (SearchStep s)]
variable [ToBackwardSearcher ρ σ]

@[specialize pat]
def defaultEndsWith (s : Slice) (pat : ρ) : Bool :=
  let searcher := ToBackwardSearcher.toSearcher s pat
  match searcher.step with
  | .yield _ (.matched _ endPos) _ => s.endPos = endPos
  | _ => false

@[specialize pat]
def defaultDropSuffix? (s : Slice) (pat : ρ) : Option s.Pos :=
  let searcher := ToBackwardSearcher.toSearcher s pat
  match searcher.step with
  | .yield _ (.matched startPos _) _ => some startPos
  | _ => none

@[always_inline, inline]
def defaultImplementation : BackwardPattern ρ where
  endsWith := defaultEndsWith
  dropSuffix? := defaultDropSuffix?

end ToBackwardSearcher

end String.Slice.Pattern
