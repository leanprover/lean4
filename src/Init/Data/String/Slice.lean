/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Init.Data.String.Pattern
public import Init.Data.Iterators.Consumers.Monadic.Collect
import Init.Data.Iterators.Combinators.FilterMap

public section

namespace String.Slice

open Pattern

@[inline]
def isEmpty (s : Slice) : Bool := s.utf8ByteSize == 0

section ForwardPatternUsers

variable {ρ : Type} {σ : Slice → Type}
variable [∀ s, Std.Iterators.Iterator (σ s) Id (SearchStep s)]
variable [∀ s, Std.Iterators.Finite (σ s) Id]
variable [∀ s, Std.Iterators.IteratorLoop (σ s) Id Id]

@[inline]
def startsWith [ForwardPattern ρ] (s : Slice) (pat : ρ) : Bool :=
  ForwardPattern.startsWith s pat

inductive SplitIterator (ρ : Type) [ToForwardSearcher ρ σ] where
  | operating (s : Slice) (currPos : s.Pos) (searcher : Std.Iter (α := σ s) (SearchStep s))
  | atEnd
  deriving Inhabited

namespace SplitIterator

variable [ToForwardSearcher ρ σ]

instance [Pure m] : Std.Iterators.Iterator (SplitIterator ρ) m Slice where
  IsPlausibleStep := fun _ _ => True
  step := fun ⟨iter⟩ =>
    match iter with
    | .operating s currPos searcher =>
      match Internal.nextMatch searcher with
      | some (searcher, startPos, endPos) =>
        let slice := s.replaceStartEnd! currPos startPos
        let nextIt := ⟨.operating s endPos searcher⟩
        pure ⟨.yield nextIt slice, by simp⟩
      | none =>
        let slice := s.replaceStart currPos
        pure ⟨.yield ⟨.atEnd⟩ slice, by simp⟩
    | .atEnd => pure ⟨.done, by simp⟩

-- TODO: Finiteness after we have a notion of lawful searcher

instance [Monad m] [Monad n] : Std.Iterators.IteratorCollect (SplitIterator ρ) m n :=
  .defaultImplementation

instance [Monad m] [Monad n] : Std.Iterators.IteratorCollectPartial (SplitIterator ρ) m n :=
  .defaultImplementation

instance [Monad m] [Monad n] : Std.Iterators.IteratorLoop (SplitIterator ρ) m n :=
  .defaultImplementation

instance [Monad m] [Monad n] : Std.Iterators.IteratorLoopPartial (SplitIterator ρ) m n :=
  .defaultImplementation

end SplitIterator

@[specialize pat]
def split [ToForwardSearcher ρ σ] (s : Slice) (pat : ρ) : Std.Iter (α := SplitIterator ρ) Slice :=
  { internalState := .operating s s.startPos (ToForwardSearcher.toSearcher s pat) }

inductive SplitInclusiveIterator (ρ : Type) [ToForwardSearcher ρ σ] where
  | operating (s : Slice) (currPos : s.Pos) (searcher : Std.Iter (α := σ s) (SearchStep s))
  | atEnd
  deriving Inhabited

namespace SplitInclusiveIterator

variable [ToForwardSearcher ρ σ]

instance [Pure m] : Std.Iterators.Iterator (SplitInclusiveIterator ρ) m Slice where
  IsPlausibleStep := fun _ _ => True
  step := fun ⟨iter⟩ =>
    match iter with
    | .operating s currPos searcher =>
      match Internal.nextMatch searcher with
      | some (searcher, _, endPos) =>
        let slice := s.replaceStartEnd! currPos endPos
        let nextIt := ⟨.operating s endPos searcher⟩
        pure ⟨.yield nextIt slice, by simp⟩
      | none =>
        if currPos != s.endPos then
          let slice := s.replaceStart currPos
          pure ⟨.yield ⟨.atEnd⟩ slice, by simp⟩
        else
          pure ⟨.done, by simp⟩
    | .atEnd => pure ⟨.done, by simp⟩

-- TODO: Finiteness after we have a notion of lawful searcher

instance [Monad m] [Monad n] : Std.Iterators.IteratorCollect (SplitInclusiveIterator ρ) m n :=
  .defaultImplementation

instance [Monad m] [Monad n] : Std.Iterators.IteratorCollectPartial (SplitInclusiveIterator ρ) m n :=
  .defaultImplementation

instance [Monad m] [Monad n] : Std.Iterators.IteratorLoop (SplitInclusiveIterator ρ) m n :=
  .defaultImplementation

instance [Monad m] [Monad n] : Std.Iterators.IteratorLoopPartial (SplitInclusiveIterator ρ) m n :=
  .defaultImplementation

end SplitInclusiveIterator

@[specialize pat]
def splitInclusive [ToForwardSearcher ρ σ] (s : Slice) (pat : ρ) : Std.Iter (α := SplitInclusiveIterator ρ) Slice :=
  { internalState := .operating s s.startPos (ToForwardSearcher.toSearcher s pat) }

@[inline]
def drop (s : Slice) (n : Nat) : Slice :=
  s.replaceStart (s.startPos.nextn n)

@[specialize pat]
def dropWhile [ToForwardSearcher ρ σ] (s : Slice) (pat : ρ) : Slice :=
  let searcher := ToForwardSearcher.toSearcher s pat
  match Internal.nextReject searcher with
  | some (_, startPos, _) => s.replaceStart startPos
  | none => s.replaceStart s.endPos

-- If we want to optimize this can be pushed further by specialising for ASCII
@[inline]
def trimAsciiStart (s : Slice) : Slice :=
  dropWhile s Char.isWhitespace

@[inline]
def take (s : Slice) (n : Nat) : Slice :=
  s.replaceEnd (s.startPos.nextn n)

@[specialize pat]
def takeWhile [ToForwardSearcher ρ σ] (s : Slice) (pat : ρ) : Slice :=
  let searcher := ToForwardSearcher.toSearcher s pat
  match Internal.nextReject searcher with
  | some (_, startPos, _) => s.replaceEnd startPos
  | none => s

@[inline]
def dropPrefix? [ForwardPattern ρ] (s : Slice) (pat : ρ) : Option Slice :=
  ForwardPattern.dropPrefix? s pat

@[specialize pat]
def dropPrefix [ForwardPattern ρ] (s : Slice) (pat : ρ) : Slice :=
  dropPrefix? s pat |>.getD s

@[specialize pat]
def find? [ToForwardSearcher ρ σ] (s : Slice) (pat : ρ) : Option s.Pos :=
  let searcher := ToForwardSearcher.toSearcher s pat
  match Internal.nextMatch searcher with
  | some (_, startPos, _) => some startPos
  | none => none

@[specialize pat]
def contains [ToForwardSearcher ρ σ] (s : Slice) (pat : ρ) : Bool :=
  let searcher := ToForwardSearcher.toSearcher s pat
  Internal.nextMatch searcher |>.isSome

@[specialize pat]
def all [ToForwardSearcher ρ σ] (s : Slice) (pat : ρ) : Bool :=
  let searcher := ToForwardSearcher.toSearcher s pat
  Internal.nextReject searcher |>.isNone

end ForwardPatternUsers

section BackwardPatternUsers

variable {σ : Slice → Type}
variable [∀ s, Std.Iterators.Iterator (σ s) Id (SearchStep s)]
variable [∀ s, Std.Iterators.Finite (σ s) Id]
variable [∀ s, Std.Iterators.IteratorLoop (σ s) Id Id]

@[inline]
def endsWith [BackwardPattern ρ] (s : Slice) (pat : ρ) : Bool :=
  BackwardPattern.endsWith s pat

-- TODO: Wait for forward splitting with this one
inductive RevSplitIterator (ρ : Type) [ToBackwardSearcher ρ σ] where
  | operating (s : Slice) (currPos : s.Pos) (searcher : Std.Iter (α := σ s) (SearchStep s))
  | atEnd
  deriving Inhabited

namespace RevSplitIterator

variable [ToBackwardSearcher ρ σ]

instance [Pure m] : Std.Iterators.Iterator (RevSplitIterator ρ) m Slice where
  IsPlausibleStep := fun _ _ => True
  step := fun ⟨iter⟩ =>
    match iter with
    | .operating s currPos searcher =>
      match Internal.nextMatch searcher with
      | some (searcher, startPos, endPos) =>
        let slice := s.replaceStartEnd! endPos currPos
        let nextIt := ⟨.operating s startPos searcher⟩
        pure ⟨.yield nextIt slice, by simp⟩
      | none =>
        if currPos ≠ s.startPos then
          let slice := s.replaceEnd currPos
          pure ⟨.yield ⟨.atEnd⟩ slice, by simp⟩
        else
          pure ⟨.done, by simp⟩
    | .atEnd => pure ⟨.done, by simp⟩

-- TODO: Finiteness after we have a notion of lawful searcher

instance [Monad m] [Monad n] : Std.Iterators.IteratorCollect (RevSplitIterator ρ) m n :=
  .defaultImplementation

instance [Monad m] [Monad n] : Std.Iterators.IteratorCollectPartial (RevSplitIterator ρ) m n :=
  .defaultImplementation

instance [Monad m] [Monad n] : Std.Iterators.IteratorLoop (RevSplitIterator ρ) m n :=
  .defaultImplementation

instance [Monad m] [Monad n] : Std.Iterators.IteratorLoopPartial (RevSplitIterator ρ) m n :=
  .defaultImplementation

end RevSplitIterator

@[specialize pat]
def revSplit [ToBackwardSearcher ρ σ] (s : Slice) (pat : ρ) :
    Std.Iter (α := RevSplitIterator ρ) Slice :=
  { internalState := .operating s s.endPos (ToBackwardSearcher.toSearcher s pat) }

@[inline]
def dropEnd (s : Slice) (n : Nat) : Slice :=
  s.replaceEnd (s.endPos.prevn n)

@[specialize pat]
def dropEndWhile [ToBackwardSearcher ρ σ] (s : Slice) (pat : ρ) : Slice :=
  let searcher := ToBackwardSearcher.toSearcher s pat
  match Internal.nextReject searcher with
  | some (_, _, endPos) => s.replaceEnd endPos
  | none => s.replaceEnd s.startPos

-- If we want to optimize this can be pushed further by specialising for ASCII
@[inline]
def trimAsciiEnd (s : Slice) : Slice :=
  dropEndWhile s Char.isWhitespace

@[inline]
def takeEnd (s : Slice) (n : Nat) : Slice :=
  s.replaceStart (s.startPos.prevn n)

@[specialize pat]
def takeEndWhile [ToBackwardSearcher ρ σ] (s : Slice) (pat : ρ) : Slice :=
  let searcher := ToBackwardSearcher.toSearcher s pat
  match Internal.nextReject searcher with
  | some (_, _, endPos) => s.replaceStart endPos
  | none => s

@[inline]
def dropSuffix? [BackwardPattern ρ] (s : Slice) (pat : ρ) : Option Slice :=
  BackwardPattern.dropSuffix? s pat

@[specialize pat]
def dropSuffix [BackwardPattern ρ] (s : Slice) (pat : ρ) : Slice :=
  dropSuffix? s pat |>.getD s

@[specialize pat]
def revFind? [ToBackwardSearcher ρ σ] (s : Slice) (pat : ρ) : Option s.Pos :=
  let searcher := ToBackwardSearcher.toSearcher s pat
  match Internal.nextMatch searcher with
  | some (_, startPos, _) => some startPos
  | none => none

end BackwardPatternUsers

def trimAscii (s : Slice) : Slice :=
  s.trimAsciiStart.trimAsciiEnd

def eqIgnoreAsciiCase (s1 s2 : Slice) : Bool :=
  s1.utf8ByteSize == s2.utf8ByteSize && go s1 s1.startPos.offset s2 s2.startPos.offset
where
  go (s1 : Slice) (s1Curr : String.Pos) (s2 : Slice) (s2Curr : String.Pos) : Bool :=
    if h : s1Curr < s1.utf8ByteSize ∧ s2Curr < s2.utf8ByteSize then
      if (s1.getUtf8Byte s1Curr h.left).toAsciiLower == (s2.getUtf8Byte s2Curr h.right).toAsciiLower then
        go s1 s1Curr.inc s2 s2Curr.inc
      else
        false
    else
      s1Curr == s1.utf8ByteSize && s2Curr == s2.utf8ByteSize
  termination_by s1.endPos.offset.byteIdx - s1Curr.byteIdx
  decreasing_by
    simp at h ⊢
    omega

def beq (s1 s2 : Slice) : Bool :=
  if h : s1.utf8ByteSize = s2.utf8ByteSize then
    have h1 := by simp [h, String.Pos.le_iff]
    have h2 := by simp [h, String.Pos.le_iff]
    Internal.memcmp s1 s2 s1.startPos.offset s2.startPos.offset s1.utf8ByteSize h1 h2
  else
    false

instance : BEq Slice where
  beq := beq

@[extern "lean_slice_hash"]
opaque hash (s : Slice) : UInt64

instance : Hashable Slice where
  hash := hash

/-
instance : Ord Slice := sorry
-/

structure CharIterator where
  s : Slice
  currPos : s.Pos
  deriving Inhabited

def chars (s : Slice) : Std.Iter (α := CharIterator) Char :=
  { internalState := { s, currPos := s.startPos }}

namespace CharIterator

instance [Pure m] : Std.Iterators.Iterator CharIterator m Char where
  IsPlausibleStep it
    | .yield it' out =>
      ∃ h1 : it.internalState.s = it'.internalState.s,
      ∃ h2 : it.internalState.currPos ≠ it.internalState.s.endPos,
        it'.internalState.currPos = h1 ▸ (it.internalState.currPos.next h2) ∧
        it.internalState.currPos.get h2 = out
    | .skip _ => False
    | .done => it.internalState.currPos = it.internalState.s.endPos
  step := fun ⟨s, currPos⟩ =>
    if h : currPos = s.endPos then
      pure ⟨.done, by simp [h]⟩
    else
      pure ⟨.yield ⟨s, currPos.next h⟩ (currPos.get h), by simp [h]⟩

private def finitenessRelation [Pure m] : Std.Iterators.FinitenessRelation CharIterator m where
  rel := InvImage WellFoundedRelation.rel
      (fun it => it.internalState.s.utf8ByteSize.byteIdx - it.internalState.currPos.offset.byteIdx)
  wf := InvImage.wf _ WellFoundedRelation.wf
  subrelation {it it'} h := by
    simp_wf
    obtain ⟨step, h, h'⟩ := h
    cases step
    · cases h
      obtain ⟨h1, h2, h3, _⟩ := h'
      have h4 := Char.utf8Size_pos (it.internalState.currPos.get h2)
      have h5 := it.internalState.currPos.isValidForSlice.le_utf8ByteSize
      rw [h3]
      clear h3
      generalize it'.internalState.s = s at *
      cases h1
      simp [Pos.ext_iff, String.Pos.ext_iff, Pos.le_iff] at h2 h4 h5 ⊢
      omega
    · cases h'
    · cases h

@[no_expose]
instance [Pure m] : Std.Iterators.Finite CharIterator m :=
  .of_finitenessRelation finitenessRelation

instance [Monad m] [Monad n] : Std.Iterators.IteratorCollect CharIterator m n :=
  .defaultImplementation

instance [Monad m] [Monad n] : Std.Iterators.IteratorCollectPartial CharIterator m n :=
  .defaultImplementation

instance [Monad m] [Monad n] : Std.Iterators.IteratorLoop CharIterator m n :=
  .defaultImplementation

instance [Monad m] [Monad n] : Std.Iterators.IteratorLoopPartial CharIterator m n :=
  .defaultImplementation

end CharIterator

structure RevCharIterator where
  s : Slice
  currPos : s.Pos
  deriving Inhabited

def revChars (s : Slice) : Std.Iter (α := RevCharIterator) Char :=
  { internalState := { s, currPos := s.endPos }}

namespace RevCharIterator

instance [Pure m] : Std.Iterators.Iterator RevCharIterator m Char where
  IsPlausibleStep it
    | .yield it' out =>
      ∃ h1 : it.internalState.s = it'.internalState.s,
      ∃ h2 : it.internalState.currPos ≠ it.internalState.s.startPos,
        it'.internalState.currPos = h1 ▸ (it.internalState.currPos.prev h2) ∧
        (it.internalState.currPos.prev h2).get Pos.prev_ne_endPos = out
    | .skip _ => False
    | .done => it.internalState.currPos = it.internalState.s.startPos
  step := fun ⟨s, currPos⟩ =>
    if h : currPos = s.startPos then
      pure ⟨.done, by simp [h]⟩
    else
      let nextPos := currPos.prev h
      pure ⟨.yield ⟨s, nextPos⟩ (nextPos.get Pos.prev_ne_endPos), by simp [h, nextPos]⟩

private def finitenessRelation [Pure m] : Std.Iterators.FinitenessRelation RevCharIterator m where
  rel := InvImage WellFoundedRelation.rel
      (fun it => it.internalState.currPos.offset.byteIdx)
  wf := InvImage.wf _ WellFoundedRelation.wf
  subrelation {it it'} h := by
    simp_wf
    obtain ⟨step, h, h'⟩ := h
    cases step
    · cases h
      obtain ⟨h1, h2, h3, _⟩ := h'
      rw [h3]
      clear h3
      generalize it'.internalState.s = s at *
      cases h1
      have h4 := Pos.offset_prev_lt_offset (h := h2)
      simp
      omega
    · cases h'
    · cases h

@[no_expose]
instance [Pure m] : Std.Iterators.Finite RevCharIterator m :=
  .of_finitenessRelation finitenessRelation

instance [Monad m] [Monad n] : Std.Iterators.IteratorCollect RevCharIterator m n :=
  .defaultImplementation

instance [Monad m] [Monad n] : Std.Iterators.IteratorCollectPartial RevCharIterator m n :=
  .defaultImplementation

instance [Monad m] [Monad n] : Std.Iterators.IteratorLoop RevCharIterator m n :=
  .defaultImplementation

instance [Monad m] [Monad n] : Std.Iterators.IteratorLoopPartial RevCharIterator m n :=
  .defaultImplementation

end RevCharIterator

structure PosIterator (s : Slice) where
  currPos : s.Pos
  deriving Inhabited

def positions (s : Slice) : Std.Iter (α := PosIterator s) s.Pos :=
  { internalState := { currPos := s.startPos }}

namespace PosIterator

instance [Pure m] : Std.Iterators.Iterator (PosIterator s) m s.Pos where
  IsPlausibleStep it
    | .yield it' out =>
      ∃ h : it.internalState.currPos ≠ s.endPos,
        it'.internalState.currPos = it.internalState.currPos.next h ∧
        it.internalState.currPos = out
    | .skip _ => False
    | .done => it.internalState.currPos = s.endPos
  step := fun ⟨⟨currPos⟩⟩ =>
    if h : currPos = s.endPos then
      pure ⟨.done, by simp [h]⟩
    else
      pure ⟨.yield ⟨⟨currPos.next h⟩⟩ currPos, by simp [h]⟩

private def finitenessRelation [Pure m] : Std.Iterators.FinitenessRelation (PosIterator s) m where
  rel := InvImage WellFoundedRelation.rel
      (fun it => s.utf8ByteSize.byteIdx - it.internalState.currPos.offset.byteIdx)
  wf := InvImage.wf _ WellFoundedRelation.wf
  subrelation {it it'} h := by
    simp_wf
    obtain ⟨step, h, h'⟩ := h
    cases step
    · cases h
      obtain ⟨h1, h2, _⟩ := h'
      have h3 := Char.utf8Size_pos (it.internalState.currPos.get h1)
      have h4 := it.internalState.currPos.isValidForSlice.le_utf8ByteSize
      simp [Pos.ext_iff, String.Pos.ext_iff, Pos.le_iff] at h1 h2 h4
      omega
    · cases h'
    · cases h

@[no_expose]
instance [Pure m] : Std.Iterators.Finite (PosIterator s) m :=
  .of_finitenessRelation finitenessRelation

instance [Monad m] [Monad n] : Std.Iterators.IteratorCollect (PosIterator s) m n :=
  .defaultImplementation

instance [Monad m] [Monad n] : Std.Iterators.IteratorCollectPartial (PosIterator s) m n :=
  .defaultImplementation

instance [Monad m] [Monad n] : Std.Iterators.IteratorLoop (PosIterator s) m n :=
  .defaultImplementation

instance [Monad m] [Monad n] : Std.Iterators.IteratorLoopPartial (PosIterator s) m n :=
  .defaultImplementation

end PosIterator

structure RevPosIterator (s : Slice) where
  currPos : s.Pos
  deriving Inhabited

def revPositions (s : Slice) : Std.Iter (α := RevPosIterator s) s.Pos :=
  { internalState := { currPos := s.endPos }}

namespace RevPosIterator

instance [Pure m] : Std.Iterators.Iterator (RevPosIterator s) m s.Pos where
  IsPlausibleStep it
    | .yield it' out =>
      ∃ h : it.internalState.currPos ≠ s.startPos,
        it'.internalState.currPos = it.internalState.currPos.prev h ∧
        it.internalState.currPos.prev h = out
    | .skip _ => False
    | .done => it.internalState.currPos = s.startPos
  step := fun ⟨⟨currPos⟩⟩ =>
    if h : currPos = s.startPos then
      pure ⟨.done, by simp [h]⟩
    else
      let prevPos := currPos.prev h
      pure ⟨.yield ⟨⟨prevPos⟩⟩ prevPos, by simp [h, prevPos]⟩

private def finitenessRelation [Pure m] : Std.Iterators.FinitenessRelation (RevPosIterator s) m where
  rel := InvImage WellFoundedRelation.rel
      (fun it => it.internalState.currPos.offset.byteIdx)
  wf := InvImage.wf _ WellFoundedRelation.wf
  subrelation {it it'} h := by
    simp_wf
    obtain ⟨step, h, h'⟩ := h
    cases step
    · cases h
      obtain ⟨h1, h2, _⟩ := h'
      have h3 := Pos.offset_prev_lt_offset (h := h1)
      simp [Pos.ext_iff, String.Pos.ext_iff] at h2 h3
      omega
    · cases h'
    · cases h

@[no_expose]
instance [Pure m] : Std.Iterators.Finite (RevPosIterator s) m :=
  .of_finitenessRelation finitenessRelation

instance [Monad m] [Monad n] : Std.Iterators.IteratorCollect (RevPosIterator s) m n :=
  .defaultImplementation

instance [Monad m] [Monad n] : Std.Iterators.IteratorCollectPartial (RevPosIterator s) m n :=
  .defaultImplementation

instance [Monad m] [Monad n] : Std.Iterators.IteratorLoop (RevPosIterator s) m n :=
  .defaultImplementation

instance [Monad m] [Monad n] : Std.Iterators.IteratorLoopPartial (RevPosIterator s) m n :=
  .defaultImplementation

end RevPosIterator

structure ByteIterator where
  s : Slice
  offset : String.Pos
  deriving Inhabited

def bytes (s : Slice) : Std.Iter (α := ByteIterator) UInt8 :=
  { internalState := { s, offset := s.startPos.offset }}

namespace ByteIterator

instance [Pure m] : Std.Iterators.Iterator ByteIterator m UInt8 where
  IsPlausibleStep it
    | .yield it' out =>
      ∃ h1 : it.internalState.offset < it.internalState.s.utf8ByteSize,
        it.internalState.s = it'.internalState.s ∧
        it'.internalState.offset = it.internalState.offset.inc ∧
        it.internalState.s.getUtf8Byte it.internalState.offset h1 = out
    | .skip _ => False
    | .done => ¬ it.internalState.offset < it.internalState.s.utf8ByteSize
  step := fun ⟨s, offset⟩ =>
    if h : offset < s.utf8ByteSize then
      pure ⟨.yield ⟨s, offset.inc⟩ (s.getUtf8Byte offset h), by simp [h]⟩
    else
      pure ⟨.done, by simp [h]⟩

private def finitenessRelation [Pure m] : Std.Iterators.FinitenessRelation (ByteIterator) m where
  rel := InvImage WellFoundedRelation.rel
      (fun it => it.internalState.s.utf8ByteSize.byteIdx - it.internalState.offset.byteIdx)
  wf := InvImage.wf _ WellFoundedRelation.wf
  subrelation {it it'} h := by
    simp_wf
    obtain ⟨step, h, h'⟩ := h
    cases step
    · cases h
      obtain ⟨h1, h2, h3, h4⟩ := h'
      clear h4
      generalize it'.internalState.s = s at *
      cases h2
      simp [String.Pos.ext_iff] at h1 h3
      omega
    · cases h'
    · cases h

@[no_expose]
instance [Pure m] : Std.Iterators.Finite ByteIterator m :=
  .of_finitenessRelation finitenessRelation

instance [Monad m] [Monad n] : Std.Iterators.IteratorCollect ByteIterator m n :=
  .defaultImplementation

instance [Monad m] [Monad n] : Std.Iterators.IteratorCollectPartial ByteIterator m n :=
  .defaultImplementation

instance [Monad m] [Monad n] : Std.Iterators.IteratorLoop ByteIterator m n :=
  .defaultImplementation

instance [Monad m] [Monad n] : Std.Iterators.IteratorLoopPartial ByteIterator m n :=
  .defaultImplementation

end ByteIterator

structure RevByteIterator where
  s : Slice
  offset : String.Pos
  hinv : offset ≤ s.utf8ByteSize

def revBytes (s : Slice) : Std.Iter (α := RevByteIterator) UInt8 :=
  { internalState := { s, offset := s.endPos.offset, hinv := by simp }}

instance : Inhabited RevByteIterator where
  default :=
    let s := default
    { s := s, offset := s.endPos.offset, hinv := by simp}

namespace RevByteIterator

instance [Pure m] : Std.Iterators.Iterator RevByteIterator m UInt8 where
  IsPlausibleStep it
    | .yield it' out =>
      ∃ h1 : it.internalState.offset.dec < it.internalState.s.utf8ByteSize,
        it.internalState.s = it'.internalState.s ∧
        it.internalState.offset ≠ 0 ∧
        it'.internalState.offset = it.internalState.offset.dec ∧
        it.internalState.s.getUtf8Byte it.internalState.offset.dec h1 = out
    | .skip _ => False
    | .done => it.internalState.offset = 0
  step := fun ⟨s, offset, hinv⟩ =>
    if h : offset ≠ 0 then
      let nextOffset := offset.dec
      have hbound := by
        simp [String.Pos.le_iff, nextOffset] at h hinv ⊢
        omega
      have hinv := by
        simp [String.Pos.le_iff, nextOffset] at hinv ⊢
        omega
      have hiter := by simp [nextOffset, hbound, h]
      pure ⟨.yield ⟨s, nextOffset, hinv⟩ (s.getUtf8Byte nextOffset hbound), hiter⟩
    else
      pure ⟨.done, by simpa using h⟩

private def finitenessRelation [Pure m] : Std.Iterators.FinitenessRelation (RevByteIterator) m where
  rel := InvImage WellFoundedRelation.rel
      (fun it => it.internalState.offset.byteIdx)
  wf := InvImage.wf _ WellFoundedRelation.wf
  subrelation {it it'} h := by
    simp_wf
    obtain ⟨step, h, h'⟩ := h
    cases step
    · cases h
      obtain ⟨h1, h2, h3, h4, h5⟩ := h'
      rw [h4]
      simp at h1 h3 ⊢
      omega
    · cases h'
    · cases h

@[no_expose]
instance [Pure m] : Std.Iterators.Finite RevByteIterator m :=
  .of_finitenessRelation finitenessRelation

instance [Monad m] [Monad n] : Std.Iterators.IteratorCollect RevByteIterator m n :=
  .defaultImplementation

instance [Monad m] [Monad n] : Std.Iterators.IteratorCollectPartial RevByteIterator m n :=
  .defaultImplementation

instance [Monad m] [Monad n] : Std.Iterators.IteratorLoop RevByteIterator m n :=
  .defaultImplementation

instance [Monad m] [Monad n] : Std.Iterators.IteratorLoopPartial RevByteIterator m n :=
  .defaultImplementation

end RevByteIterator

def lines.lineMap (s : Slice) : Slice :=
  if let some s := s.dropSuffix? '\n' then
    if let some s := s.dropSuffix? '\r' then
      s
    else
      s
  else
    s

def lines (s : Slice) :=
  s.splitInclusive '\n' |>.map lines.lineMap

end String.Slice
