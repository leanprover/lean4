/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Init.Data.String.Basic
public import Init.Data.Iterators.Basic

/-!
This module defines the notion of patterns which is central to the `Slice` and `String` API.
All functions on `Slice` and `String` that "search for something" are polymorphic over a pattern
instead of taking just one particular kind of pattern such as a `Char`. The key components are:
- `ToForwardSearcher`
- `ForwardPattern`
- `ToBackwardSearcher`
- `SuffixPattern`
-/

public section

namespace String.Slice.Pattern

/--
A step taken during the traversal of a `Slice` by a forward or backward searcher.
-/
inductive SearchStep (s : Slice) where
  /--
  The subslice starting at `startPos` and ending at `endPos` did not match the pattern.
  -/
  | rejected (startPos endPos : s.Pos)
  /--
  The subslice starting at `startPos` and ending at `endPos` did not match the pattern.
  -/
  | matched (startPos endPos : s.Pos)
  deriving Inhabited

/--
Provides a conversion from a pattern to an iterator of `SearchStep` searching for matches of the
pattern from the start towards the end of a `Slice`.
-/
class ToForwardSearcher (ρ : Type) (σ : outParam (Slice → Type)) where
  /--
  Build an iterator of `SearchStep` corresponding to matches of `pat` along the slice `s`.
  The `SearchStep`s returned by this iterator must contain ranges that are adjacent, non-overlapping
  and cover all of `s`.
  -/
  toSearcher : (s : Slice) → (pat : ρ) → Std.Iter (α := σ s) (SearchStep s)

/--
Provides simple pattern matching capabilities from the start of a `Slice`.

While these operations can be implemented on top of `ToForwardSearcher` some patterns allow for more
efficient implementations so this class can be used to specialise for them. If there is no need to
specialise in this fashion `ForwardPattern.defaultImplementation` can be used to automatically
derive an instance.
-/
class ForwardPattern (ρ : Type) where
  /--
  Checks whether the slice starts with the pattern.
  -/
  startsWith : Slice → ρ → Bool
  /--
  Checks whether the slice starts with the pattern, if it does return slice with the prefix removed,
  otherwise `none`.
  -/
  dropPrefix? : Slice → ρ → Option Slice

namespace Internal

@[extern "lean_slice_memcmp"]
def memcmp (lhs rhs : Slice) (lstart : String.Pos) (rstart : String.Pos) (len : String.Pos)
    (h1 : lstart + len ≤ lhs.utf8ByteSize) (h2 : rstart + len ≤ rhs.utf8ByteSize) : Bool :=
  go 0
where
  go (curr : String.Pos) : Bool :=
    if h : curr < len then
      have hl := by
        simp [Pos.le_iff] at h h1 ⊢
        omega
      have hr := by
        simp [Pos.le_iff] at h h2 ⊢
        omega
      if lhs.getUtf8Byte (lstart + curr) hl == rhs.getUtf8Byte (rstart + curr) hr then
        go curr.inc
      else
        false
    else
      true
  termination_by len.byteIdx - curr.byteIdx
  decreasing_by
    simp at h ⊢
    omega

variable {ρ : Type} {σ : Slice → Type}
variable [∀ s, Std.Iterators.Iterator (σ s) Id (SearchStep s)]
variable [∀ s, Std.Iterators.Finite (σ s) Id]

/--
Tries to skip the `searcher` until the next `SearchStep.matched` and return it. If no match is
found until the end returns `none`.
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
Tries to skip the `searcher` until the next `SearchStep.rejected` and return it. If no reject is
found until the end returns `none`.
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
def defaultDropPrefix? (s : Slice) (pat : ρ) : Option Slice :=
  let searcher := ToForwardSearcher.toSearcher s pat
  match searcher.step with
  | .yield _ (.matched _ endPos) _ => some (s.replaceStart endPos)
  | _ => none

@[always_inline, inline]
def defaultImplementation : ForwardPattern ρ where
  startsWith := defaultStartsWith
  dropPrefix? := defaultDropPrefix?

end ForwardPattern

/--
Provides a conversion from a pattern to an iterator of `SearchStep` searching for matches of the
pattern from the end towards the start of a `Slice`.
-/
class ToBackwardSearcher (ρ : Type) (σ : outParam (Slice → Type)) where
  /--
  Build an iterator of `SearchStep` corresponding to matches of `pat` along the slice `s`.
  The `SearchStep`s returned by this iterator must contain ranges that are adjacent, non-overlapping
  and cover all of `s`.
  -/
  toSearcher : (s : Slice) → ρ → Std.Iter (α := σ s) (SearchStep s)

/--
Provides simple pattern matching capabilities from the end of a `Slice`.

While these operations can be implemented on top of `ToBackwardSearcher` some patterns allow for
more efficient implementations so this class can be used to specialise for them. If there is no
need to specialise in this fashion `BackwardPattern.defaultImplementation` can be used to
automatically derive an instance.
-/
class BackwardPattern (ρ : Type) where
  endsWith : Slice → ρ → Bool
  dropSuffix? : Slice → ρ → Option Slice

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
def defaultDropSuffix? (s : Slice) (pat : ρ) : Option Slice :=
  let searcher := ToBackwardSearcher.toSearcher s pat
  match searcher.step with
  | .yield _ (.matched startPos _) _ => some (s.replaceEnd startPos)
  | _ => none

@[always_inline, inline]
def defaultImplementation : BackwardPattern ρ where
  endsWith := defaultEndsWith
  dropSuffix? := defaultDropSuffix?

end ToBackwardSearcher

end String.Slice.Pattern
