/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Init.Data.String.Pattern.Basic
public import Init.Data.Iterators.Internal.Termination
public import Init.Data.Iterators.Consumers.Monadic.Loop

set_option doc.verso true

/-!
This module defines the necessary instances to register {name}`Char` with the pattern framework.
-/

public section

namespace String.Slice.Pattern

structure ForwardCharSearcher (s : Slice) where
  currPos : s.Pos
  needle : Char
deriving Inhabited

namespace ForwardCharSearcher

@[inline]
def iter (s : Slice) (c : Char) : Std.Iter (α := ForwardCharSearcher s) (SearchStep s) :=
  { internalState := { currPos := s.startPos, needle := c }}

instance (s : Slice) : Std.Iterators.Iterator (ForwardCharSearcher s) Id (SearchStep s) where
  IsPlausibleStep it
    | .yield it' out =>
      it.internalState.needle = it'.internalState.needle ∧
      ∃ h1 : it.internalState.currPos ≠ s.endPos,
        it'.internalState.currPos = it.internalState.currPos.next h1 ∧
        match out with
        | .matched startPos endPos =>
          it.internalState.currPos = startPos ∧
          it'.internalState.currPos = endPos ∧
          it.internalState.currPos.get h1 = it.internalState.needle
        | .rejected startPos endPos =>
          it.internalState.currPos = startPos ∧
          it'.internalState.currPos = endPos ∧
          it.internalState.currPos.get h1 ≠ it.internalState.needle
    | .skip _ => False
    | .done => it.internalState.currPos = s.endPos
  step := fun ⟨currPos, needle⟩ =>
    if h1 : currPos = s.endPos then
      pure ⟨.done, by simp [h1]⟩
    else
      let nextPos := currPos.next h1
      let nextIt := ⟨nextPos, needle⟩
      if h2 : currPos.get h1 = needle then
        pure ⟨.yield nextIt (.matched currPos nextPos), by simp [h1, h2, nextIt, nextPos]⟩
      else
        pure ⟨.yield nextIt (.rejected currPos nextPos), by simp [h1, h2, nextIt, nextPos]⟩

def finitenessRelation : Std.Iterators.FinitenessRelation (ForwardCharSearcher s) Id where
  rel := InvImage WellFoundedRelation.rel
      (fun it => s.utf8ByteSize.byteIdx - it.internalState.currPos.offset.byteIdx)
  wf := InvImage.wf _ WellFoundedRelation.wf
  subrelation {it it'} h := by
    simp_wf
    obtain ⟨step, h, h'⟩ := h
    cases step
    · cases h
      obtain ⟨_, h1, h2, _⟩ := h'
      have h3 := Char.utf8Size_pos (it.internalState.currPos.get h1)
      have h4 := it.internalState.currPos.isValidForSlice.le_utf8ByteSize
      simp [Pos.ext_iff, String.Pos.Raw.ext_iff, Pos.Raw.le_iff] at h1 h2 h4
      omega
    · cases h'
    · cases h

instance : Std.Iterators.Finite (ForwardCharSearcher s) Id :=
  .of_finitenessRelation finitenessRelation

instance : Std.Iterators.IteratorLoop (ForwardCharSearcher s) Id Id :=
  .defaultImplementation

instance : ToForwardSearcher Char ForwardCharSearcher where
  toSearcher := iter

instance : ForwardPattern Char := .defaultImplementation

end ForwardCharSearcher

structure BackwardCharSearcher (s : Slice) where
  currPos : s.Pos
  needle : Char
deriving Inhabited

namespace BackwardCharSearcher

@[inline]
def iter (s : Slice) (c : Char) : Std.Iter (α := BackwardCharSearcher s) (SearchStep s) :=
  { internalState := { currPos := s.endPos, needle := c }}

instance (s : Slice) : Std.Iterators.Iterator (BackwardCharSearcher s) Id (SearchStep s) where
  IsPlausibleStep it
    | .yield it' out =>
      it.internalState.needle = it'.internalState.needle ∧
      ∃ h1 : it.internalState.currPos ≠ s.startPos,
        it'.internalState.currPos = it.internalState.currPos.prev h1 ∧
        match out with
        | .matched startPos endPos =>
          it.internalState.currPos = endPos ∧
          it'.internalState.currPos = startPos ∧
          (it.internalState.currPos.prev h1).get Pos.prev_ne_endPos = it.internalState.needle
        | .rejected startPos endPos =>
          it.internalState.currPos = endPos ∧
          it'.internalState.currPos = startPos ∧
          (it.internalState.currPos.prev h1).get Pos.prev_ne_endPos ≠ it.internalState.needle
    | .skip _ => False
    | .done => it.internalState.currPos = s.startPos
  step := fun ⟨currPos, needle⟩ =>
    if h1 : currPos = s.startPos then
      pure ⟨.done, by simp [h1]⟩
    else
      let nextPos := currPos.prev h1
      let nextIt := ⟨nextPos, needle⟩
      if h2 : nextPos.get Pos.prev_ne_endPos = needle then
        pure ⟨.yield nextIt (.matched nextPos currPos), by simp [h1, h2, nextIt, nextPos]⟩
      else
        pure ⟨.yield nextIt (.rejected nextPos currPos), by simp [h1, h2, nextIt, nextPos]⟩

def finitenessRelation : Std.Iterators.FinitenessRelation (BackwardCharSearcher s) Id where
  rel := InvImage WellFoundedRelation.rel
      (fun it => it.internalState.currPos.offset.byteIdx)
  wf := InvImage.wf _ WellFoundedRelation.wf
  subrelation {it it'} h := by
    simp_wf
    obtain ⟨step, h, h'⟩ := h
    cases step
    · cases h
      obtain ⟨_, h1, h2, _⟩ := h'
      have h3 := Pos.offset_prev_lt_offset (h := h1)
      simp [Pos.ext_iff, String.Pos.Raw.ext_iff] at h2 h3
      omega
    · cases h'
    · cases h

instance : Std.Iterators.Finite (BackwardCharSearcher s) Id :=
  .of_finitenessRelation finitenessRelation

instance : Std.Iterators.IteratorLoop (BackwardCharSearcher s) Id Id :=
  .defaultImplementation

instance : ToBackwardSearcher Char BackwardCharSearcher where
  toSearcher := iter

instance : BackwardPattern Char := ToBackwardSearcher.defaultImplementation

end BackwardCharSearcher

end String.Slice.Pattern
