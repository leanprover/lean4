/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Init.Data.String.Pattern.Basic
public import Init.Data.Iterators.Consumers.Monadic.Loop
import Init.Data.String.Termination

set_option doc.verso true

/-!
This module defines the necessary instances to register {name}`Char` with the pattern framework.
-/

public section

namespace String.Slice.Pattern

structure ForwardCharSearcher (needle : Char) (s : Slice) where
  currPos : s.Pos
deriving Inhabited

namespace ForwardCharSearcher

@[inline]
def iter (c : Char) (s : Slice) : Std.Iter (α := ForwardCharSearcher c s) (SearchStep s) :=
  { internalState := { currPos := s.startPos }}

instance (s : Slice) : Std.Iterator (ForwardCharSearcher c s) Id (SearchStep s) where
  IsPlausibleStep it
    | .yield it' out =>
      ∃ h1 : it.internalState.currPos ≠ s.endPos,
        it'.internalState.currPos = it.internalState.currPos.next h1 ∧
        match out with
        | .matched startPos endPos =>
          it.internalState.currPos = startPos ∧
          it'.internalState.currPos = endPos ∧
          it.internalState.currPos.get h1 = c
        | .rejected startPos endPos =>
          it.internalState.currPos = startPos ∧
          it'.internalState.currPos = endPos ∧
          it.internalState.currPos.get h1 ≠ c
    | .skip _ => False
    | .done => it.internalState.currPos = s.endPos
  step := fun ⟨⟨currPos⟩⟩ =>
    if h1 : currPos = s.endPos then
      pure (.deflate ⟨.done, by simp [h1]⟩)
    else
      let nextPos := currPos.next h1
      let nextIt := ⟨⟨nextPos⟩⟩
      if h2 : currPos.get h1 = c then
        pure (.deflate ⟨.yield nextIt (.matched currPos nextPos), by simp [h1, h2, nextIt, nextPos]⟩)
      else
        pure (.deflate ⟨.yield nextIt (.rejected currPos nextPos), by simp [h1, h2, nextIt, nextPos]⟩)

def finitenessRelation : Std.Iterators.FinitenessRelation (ForwardCharSearcher s c) Id where
  Rel := InvImage WellFoundedRelation.rel (fun it => it.internalState.currPos)
  wf := InvImage.wf _ WellFoundedRelation.wf
  subrelation {it it'} h := by
    simp_wf
    obtain ⟨step, h, h'⟩ := h
    cases step
    · cases h
      obtain ⟨_, h2, _⟩ := h'
      simp [h2]
    · cases h'
    · cases h

instance : Std.Iterators.Finite (ForwardCharSearcher s c) Id :=
  .of_finitenessRelation finitenessRelation

instance : Std.IteratorLoop (ForwardCharSearcher s c) Id Id :=
  .defaultImplementation

instance {c : Char} : ToForwardSearcher c (ForwardCharSearcher c) where
  toSearcher := iter c

instance {c : Char} : ForwardPattern c := .defaultImplementation

end ForwardCharSearcher

structure BackwardCharSearcher (s : Slice) where
  currPos : s.Pos
  needle : Char
deriving Inhabited

namespace BackwardCharSearcher

@[inline]
def iter (c : Char) (s : Slice) : Std.Iter (α := BackwardCharSearcher s) (SearchStep s) :=
  { internalState := { currPos := s.endPos, needle := c }}

instance (s : Slice) : Std.Iterator (BackwardCharSearcher s) Id (SearchStep s) where
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
      pure (.deflate ⟨.done, by simp [h1]⟩)
    else
      let nextPos := currPos.prev h1
      let nextIt := ⟨nextPos, needle⟩
      if h2 : nextPos.get Pos.prev_ne_endPos = needle then
        pure (.deflate ⟨.yield nextIt (.matched nextPos currPos), by simp [h1, h2, nextIt, nextPos]⟩)
      else
        pure (.deflate ⟨.yield nextIt (.rejected nextPos currPos), by simp [h1, h2, nextIt, nextPos]⟩)

def finitenessRelation : Std.Iterators.FinitenessRelation (BackwardCharSearcher s) Id where
  Rel := InvImage WellFoundedRelation.rel (fun it => it.internalState.currPos.down)
  wf := InvImage.wf _ WellFoundedRelation.wf
  subrelation {it it'} h := by
    simp_wf
    obtain ⟨step, h, h'⟩ := h
    cases step
    · cases h
      obtain ⟨_, h1, h2, _⟩ := h'
      simp [h2]
    · cases h'
    · cases h

instance : Std.Iterators.Finite (BackwardCharSearcher s) Id :=
  .of_finitenessRelation finitenessRelation

instance : Std.IteratorLoop (BackwardCharSearcher s) Id Id :=
  .defaultImplementation

instance {c : Char} : ToBackwardSearcher c BackwardCharSearcher where
  toSearcher := iter c

instance {c : Char} : BackwardPattern c := ToBackwardSearcher.defaultImplementation

end BackwardCharSearcher

end String.Slice.Pattern
