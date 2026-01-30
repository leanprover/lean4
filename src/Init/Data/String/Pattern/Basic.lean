/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Init.Data.String.Basic
public import Init.Data.Iterators.Basic
public import Init.Data.Iterators.Consumers.Loop
import Init.Data.String.Lemmas.SliceIsEmpty
import Init.Data.String.Termination
import Init.Data.String.Grind
import Init.Data.String.Lemmas.Order

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

namespace SearchStep

def startPos {s : Slice} (st : SearchStep s) : s.Pos :=
  match st with
  | .rejected startPos _ => startPos
  | .matched startPos _ => startPos

@[simp]
theorem startPos_rejected {s : Slice} {p q : s.Pos} : (SearchStep.rejected p q).startPos = p := (rfl)

@[simp]
theorem startPos_matched {s : Slice} {p q : s.Pos} : (SearchStep.matched p q).startPos = p := (rfl)

def endPos {s : Slice} (st : SearchStep s) : s.Pos :=
  match st with
  | .rejected _ endPos => endPos
  | .matched _ endPos => endPos

@[simp]
theorem endPos_rejected {s : Slice} {p q : s.Pos} : (SearchStep.rejected p q).endPos = q := (rfl)

@[simp]
theorem endPos_matched {s : Slice} {p q : s.Pos} : (SearchStep.matched p q).endPos = q := (rfl)

def ofSliceFrom {s : Slice} {p : s.Pos} (st : SearchStep (s.sliceFrom p)) : SearchStep s :=
  match st with
  | .rejected l r => .rejected (Slice.Pos.ofSliceFrom l) (Slice.Pos.ofSliceFrom r)
  | .matched l r => .matched (Slice.Pos.ofSliceFrom l) (Slice.Pos.ofSliceFrom r)

@[simp]
theorem startPos_ofSliceFrom {s : Slice} {p : s.Pos} {st : SearchStep (s.sliceFrom p)} :
    st.ofSliceFrom.startPos = Slice.Pos.ofSliceFrom st.startPos := by
  cases st <;>  simp [ofSliceFrom]

@[simp]
theorem endPos_ofSliceFrom {s : Slice} {p : s.Pos} {st : SearchStep (s.sliceFrom p)} :
    st.ofSliceFrom.endPos = Slice.Pos.ofSliceFrom st.endPos := by
  cases st <;> simp [ofSliceFrom]

end SearchStep

/--
Provides simple pattern matching capabilities from the start of a {name}`Slice`.

-/
class ForwardPattern {ρ : Type} (pat : ρ) where
  /--
  Checks whether the slice starts with the pattern. If it does, the slice is returned with the
  prefix removed; otherwise the result is {name}`none`.
  -/
  dropPrefix? : (s : Slice) →  Option s.Pos
  /--
  Checks whether the slice starts with the pattern. If it does, the slice is returned with the
  prefix removed; otherwise the result is {name}`none`.
  -/
  dropPrefixOfNonempty? : (s : Slice) → (h : s.isEmpty = false) → Option s.Pos := fun s _ => dropPrefix? s
  /--
  Checks whether the slice starts with the pattern.
  -/
  startsWith : (s : Slice) → Bool := fun s => (dropPrefix? s).isSome

class LawfulForwardPattern {ρ : Type} (pat : ρ) [ForwardPattern pat] : Prop where
  dropPrefixOfNonempty?_eq {s : Slice} (h) :
    ForwardPattern.dropPrefixOfNonempty? pat s h = ForwardPattern.dropPrefix? pat s
  startsWith_eq (s : Slice) :
    ForwardPattern.startsWith pat s = (ForwardPattern.dropPrefix? pat s).isSome

class StrictForwardPattern {ρ : Type} (pat : ρ) [ForwardPattern pat] : Prop where
  ne_startPos {s : Slice} (h) (q) :
    ForwardPattern.dropPrefixOfNonempty? pat s h = some q → q ≠ s.startPos

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

namespace ToForwardSearcher

structure DefaultForwardSearcher {ρ : Type} (pat : ρ) (s : Slice) where
  currPos : s.Pos
deriving Inhabited

namespace DefaultForwardSearcher

variable {ρ : Type} (pat : ρ)

@[inline]
def iter (s : Slice) : Std.Iter (α := DefaultForwardSearcher pat s) (SearchStep s) :=
  ⟨⟨s.startPos⟩⟩

instance (s : Slice) [ForwardPattern pat] :
    Std.Iterator (DefaultForwardSearcher pat s) Id (SearchStep s) where
  IsPlausibleStep it
    | .yield it' (.rejected p₁ p₂) => ∃ (h : it.internalState.currPos ≠ s.endPos),
      ForwardPattern.dropPrefixOfNonempty? pat (s.sliceFrom it.internalState.currPos) (by simpa) = none ∧
      p₁ = it.internalState.currPos ∧ p₂ = it.internalState.currPos.next h ∧
      it'.internalState.currPos = it.internalState.currPos.next h
    | .yield it' (.matched p₁ p₂) => ∃ (h : it.internalState.currPos ≠ s.endPos), ∃ pos,
      ForwardPattern.dropPrefixOfNonempty? pat (s.sliceFrom it.internalState.currPos) (by simpa) = some pos ∧
      p₁ = it.internalState.currPos ∧ p₂ = Slice.Pos.ofSliceFrom pos ∧
      it'.internalState.currPos = Slice.Pos.ofSliceFrom pos
    | .done => it.internalState.currPos = s.endPos
    | .skip _ => False
  step it :=
    if h : it.internalState.currPos = s.endPos then
      pure (.deflate ⟨.done, by simp [h]⟩)
    else
      match h' : ForwardPattern.dropPrefixOfNonempty? pat (s.sliceFrom it.internalState.currPos) (by simpa) with
      | some pos =>
        pure (.deflate ⟨.yield ⟨⟨Slice.Pos.ofSliceFrom pos⟩⟩
          (.matched it.internalState.currPos (Slice.Pos.ofSliceFrom pos)), by simp [h, h']⟩)
      | none =>
        pure (.deflate ⟨.yield ⟨⟨it.internalState.currPos.next h⟩⟩
          (.rejected it.internalState.currPos (it.internalState.currPos.next h)), by simp [h, h']⟩)

def finitenessRelation (s : Slice) [ForwardPattern pat] [StrictForwardPattern pat] :
    Std.Iterators.FinitenessRelation (DefaultForwardSearcher pat s) Id where
  Rel := InvImage WellFoundedRelation.rel (fun it => it.internalState.currPos)
  wf := InvImage.wf _ WellFoundedRelation.wf
  subrelation {it it'} h := by
    simp_wf
    obtain ⟨step, h, h'⟩ := h
    match step with
    | .yield it'' (.rejected p₁ p₂) =>
      obtain ⟨_, ⟨-, -, -, h'⟩⟩ := h'
      cases h
      simp [h']
    | .yield it'' (.matched p₁ p₂) =>
      obtain ⟨_, pos, ⟨h₀, -, -, h'⟩⟩ := h'
      cases h
      have := StrictForwardPattern.ne_startPos _ _ h₀
      rw [h']
      exact Std.lt_of_le_of_lt Slice.Pos.le_ofSliceFrom
        (Slice.Pos.ofSliceFrom_lt_ofSliceFrom_iff.2 ((Slice.Pos.startPos_lt_iff _).2 this))

instance {s : Slice} [ForwardPattern pat] [StrictForwardPattern pat] :
    Std.Iterators.Finite (DefaultForwardSearcher pat s) Id :=
  .of_finitenessRelation (finitenessRelation pat s)

instance [ForwardPattern pat] : Std.IteratorLoop (DefaultForwardSearcher pat s) Id Id :=
  .defaultImplementation

end DefaultForwardSearcher

@[inline]
def defaultImplementation [ForwardPattern pat] : ToForwardSearcher pat (DefaultForwardSearcher pat) where
  toSearcher := DefaultForwardSearcher.iter pat

end ToForwardSearcher

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

-- namespace ForwardPattern

-- variable {ρ : Type} {σ : Slice → Type}
-- variable [∀ s, Std.Iterator (σ s) Id (SearchStep s)]
-- variable (pat : ρ) [ToForwardSearcher pat σ]

-- @[specialize pat]
-- def defaultStartsWith (s : Slice) [Std.IteratorLoop (σ s) Id Id] : Bool :=
--   let searcher := ToForwardSearcher.toSearcher pat s
--   match searcher.first? with
--   | some (.matched start ..) => s.startPos = start
--   | _ => false

-- @[specialize pat]
-- def defaultDropPrefix? (s : Slice) [Std.IteratorLoop (σ s) Id Id] : Option s.Pos :=
--   let searcher := ToForwardSearcher.toSearcher pat s
--   match searcher.first? with
--   | some (.matched _ endPos) => some endPos
--   | _ => none

-- @[always_inline, inline]
-- def defaultImplementation {pat : ρ} [ToForwardSearcher pat σ] [∀ s, Std.IteratorLoop (σ s) Id Id] :
--     ForwardPattern pat where
--   startsWith s := defaultStartsWith pat s
--   dropPrefix? s := defaultDropPrefix? pat s

-- end ForwardPattern

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
def defaultEndsWith (s : Slice) [Std.IteratorLoop (σ s) Id Id] : Bool :=
  let searcher := ToBackwardSearcher.toSearcher pat s
  match searcher.first? with
  | some (.matched _ endPos) => s.endPos = endPos
  | _ => false

@[specialize pat]
def defaultDropSuffix? (s : Slice) [Std.IteratorLoop (σ s) Id Id] : Option s.Pos :=
  let searcher := ToBackwardSearcher.toSearcher pat s
  match searcher.first? with
  | some (.matched startPos _) => some startPos
  | _ => none

@[always_inline, inline]
def defaultImplementation {pat : ρ} [ToBackwardSearcher pat σ] [∀ s, Std.IteratorLoop (σ s) Id Id] :
    BackwardPattern pat where
  endsWith s := defaultEndsWith pat s
  dropSuffix? s := defaultDropSuffix? pat s

end ToBackwardSearcher

end String.Slice.Pattern
