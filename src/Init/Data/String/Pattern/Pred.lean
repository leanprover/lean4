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

/-!
This module defines the necessary instances to register `Char → Bool` with the pattern framework.
-/

public section

namespace String.Slice.Pattern

structure ForwardCharPredSearcher (s : Slice) where
  currPos : s.Pos
  needle : Char → Bool
  deriving Inhabited

namespace ForwardCharPredSearcher

@[inline]
def iter (s : Slice) (p : Char → Bool) : Std.Iter (α := ForwardCharPredSearcher s) (SearchStep s) :=
  { internalState := { currPos := s.startPos, needle := p }}

instance (s : Slice) : Std.Iterators.Iterator (ForwardCharPredSearcher s) Id (SearchStep s) where
  IsPlausibleStep it
    | .yield it' out =>
      it.internalState.needle = it'.internalState.needle ∧
      ∃ h1 : it.internalState.currPos ≠ s.endPos,
        it'.internalState.currPos = it.internalState.currPos.next h1 ∧
        match out with
        | .matched startPos endPos =>
          it.internalState.currPos = startPos ∧
          it'.internalState.currPos = endPos ∧
          it.internalState.needle (it.internalState.currPos.get h1)
        | .rejected startPos endPos =>
          it.internalState.currPos = startPos ∧
          it'.internalState.currPos = endPos ∧
          ¬ it.internalState.needle (it.internalState.currPos.get h1)
    | .skip _ => False
    | .done => it.internalState.currPos = s.endPos
  step := fun ⟨currPos, needle⟩ =>
    if h1 : currPos = s.endPos then
      pure ⟨.done, by simp [h1]⟩
    else
      let nextPos := currPos.next h1
      let nextIt := ⟨nextPos, needle⟩
      if h2 : needle <| currPos.get h1 then
        pure ⟨.yield nextIt (.matched currPos nextPos), by simp [h1, h2, nextPos, nextIt]⟩
      else
        pure ⟨.yield nextIt (.rejected currPos nextPos), by simp [h1, h2, nextPos, nextIt]⟩


def finitenessRelation : Std.Iterators.FinitenessRelation (ForwardCharPredSearcher s) Id where
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
      simp [Pos.ext_iff, String.Pos.ext_iff, Pos.le_iff] at h1 h2 h4
      omega
    · cases h'
    · cases h

instance : Std.Iterators.Finite (ForwardCharPredSearcher s) Id :=
  .of_finitenessRelation finitenessRelation

instance : Std.Iterators.IteratorLoop (ForwardCharPredSearcher s) Id Id :=
  .defaultImplementation

instance : ToForwardSearcher (Char → Bool) ForwardCharPredSearcher where
  toSearcher := iter

instance : ForwardPattern (Char → Bool) := .defaultImplementation

end ForwardCharPredSearcher

structure BackwardCharPredSearcher (s : Slice) where
  currPos : s.Pos
  needle : Char → Bool
  deriving Inhabited

namespace BackwardCharPredSearcher

@[inline]
def iter (s : Slice) (c : Char → Bool) : Std.Iter (α := BackwardCharPredSearcher s) (SearchStep s) :=
  { internalState := { currPos := s.endPos, needle := c }}

instance (s : Slice) : Std.Iterators.Iterator (BackwardCharPredSearcher s) Id (SearchStep s) where
  IsPlausibleStep it
    | .yield it' out =>
      it.internalState.needle = it'.internalState.needle ∧
      ∃ h1 : it.internalState.currPos ≠ s.startPos,
        it'.internalState.currPos = it.internalState.currPos.prev h1 ∧
        match out with
        | .matched startPos endPos =>
          it.internalState.currPos = endPos ∧
          it'.internalState.currPos = startPos ∧
          it.internalState.needle ((it.internalState.currPos.prev h1).get Pos.prev_ne_endPos)
        | .rejected startPos endPos =>
          it.internalState.currPos = endPos ∧
          it'.internalState.currPos = startPos ∧
          ¬ it.internalState.needle ((it.internalState.currPos.prev h1).get Pos.prev_ne_endPos)
    | .skip _ => False
    | .done => it.internalState.currPos = s.startPos
  step := fun ⟨currPos, needle⟩ =>
    if h1 : currPos = s.startPos then
      pure ⟨.done, by simp [h1]⟩
    else
      let nextPos := currPos.prev h1
      let nextIt := ⟨nextPos, needle⟩
      if h2 : needle <| nextPos.get Pos.prev_ne_endPos then
        pure ⟨.yield nextIt (.matched nextPos currPos), by simp [h1, h2, nextIt, nextPos]⟩
      else
        pure ⟨.yield nextIt (.rejected nextPos currPos), by simp [h1, h2, nextIt, nextPos]⟩

def finitenessRelation : Std.Iterators.FinitenessRelation (BackwardCharPredSearcher s) Id where
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
      simp [Pos.ext_iff, String.Pos.ext_iff] at h2 h3
      omega
    · cases h'
    · cases h

instance : Std.Iterators.Finite (BackwardCharPredSearcher s) Id :=
  .of_finitenessRelation finitenessRelation

instance : Std.Iterators.IteratorLoop (BackwardCharPredSearcher s) Id Id :=
  .defaultImplementation

instance : ToBackwardSearcher (Char → Bool) BackwardCharPredSearcher where
  toSearcher := iter

instance : BackwardPattern (Char → Bool) := ToBackwardSearcher.defaultImplementation

end BackwardCharPredSearcher

end String.Slice.Pattern
