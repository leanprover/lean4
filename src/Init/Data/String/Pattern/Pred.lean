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
This module defines the necessary instances to register {lean}`Char → Bool` with the pattern
framework.
-/

public section

namespace String.Slice.Pattern

structure ForwardCharPredSearcher (p : Char → Bool) (s : Slice) where
  currPos : s.Pos
deriving Inhabited

namespace ForwardCharPredSearcher

@[inline]
def iter (p : Char → Bool) (s : Slice) : Std.Iter (α := ForwardCharPredSearcher p s) (SearchStep s) :=
  { internalState := { currPos := s.startPos }}

instance (s : Slice) : Std.Iterator (ForwardCharPredSearcher p s) Id (SearchStep s) where
  IsPlausibleStep it
    | .yield it' out =>
      ∃ h1 : it.internalState.currPos ≠ s.endPos,
        it'.internalState.currPos = it.internalState.currPos.next h1 ∧
        match out with
        | .matched startPos endPos =>
          it.internalState.currPos = startPos ∧
          it'.internalState.currPos = endPos ∧
          p (it.internalState.currPos.get h1)
        | .rejected startPos endPos =>
          it.internalState.currPos = startPos ∧
          it'.internalState.currPos = endPos ∧
          ¬ p (it.internalState.currPos.get h1)
    | .skip _ => False
    | .done => it.internalState.currPos = s.endPos
  step := fun ⟨⟨currPos⟩⟩ =>
    if h1 : currPos = s.endPos then
      pure (.deflate ⟨.done, by simp [h1]⟩)
    else
      let nextPos := currPos.next h1
      let nextIt := ⟨⟨nextPos⟩⟩
      if h2 : p <| currPos.get h1 then
        pure (.deflate ⟨.yield nextIt (.matched currPos nextPos), by simp [h1, h2, nextPos, nextIt]⟩)
      else
        pure (.deflate ⟨.yield nextIt (.rejected currPos nextPos), by simp [h1, h2, nextPos, nextIt]⟩)


def finitenessRelation : Std.Iterators.FinitenessRelation (ForwardCharPredSearcher p s) Id where
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

instance : Std.Iterators.Finite (ForwardCharPredSearcher p s) Id :=
  .of_finitenessRelation finitenessRelation

instance : Std.IteratorLoop (ForwardCharPredSearcher p s) Id Id :=
  .defaultImplementation

@[default_instance]
instance {p : Char → Bool} : ToForwardSearcher p (ForwardCharPredSearcher p) where
  toSearcher := iter p

@[default_instance]
instance {p : Char → Bool} : ForwardPattern p := .defaultImplementation

instance {p : Char → Prop} [DecidablePred p] : ToForwardSearcher p (ForwardCharPredSearcher p) where
  toSearcher := iter (decide <| p ·)

instance {p : Char → Prop} [DecidablePred p] : ForwardPattern p :=
  .defaultImplementation

end ForwardCharPredSearcher

structure BackwardCharPredSearcher (s : Slice) where
  currPos : s.Pos
  needle : Char → Bool
deriving Inhabited

namespace BackwardCharPredSearcher

@[inline]
def iter (c : Char → Bool) (s : Slice) : Std.Iter (α := BackwardCharPredSearcher s) (SearchStep s) :=
  { internalState := { currPos := s.endPos, needle := c }}

instance (s : Slice) : Std.Iterator (BackwardCharPredSearcher s) Id (SearchStep s) where
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
      pure (.deflate ⟨.done, by simp [h1]⟩)
    else
      let nextPos := currPos.prev h1
      let nextIt := ⟨nextPos, needle⟩
      if h2 : needle <| nextPos.get Pos.prev_ne_endPos then
        pure (.deflate ⟨.yield nextIt (.matched nextPos currPos), by simp [h1, h2, nextIt, nextPos]⟩)
      else
        pure (.deflate ⟨.yield nextIt (.rejected nextPos currPos), by simp [h1, h2, nextIt, nextPos]⟩)

def finitenessRelation : Std.Iterators.FinitenessRelation (BackwardCharPredSearcher s) Id where
  Rel := InvImage WellFoundedRelation.rel
      (fun it => it.internalState.currPos.offset.byteIdx)
  wf := InvImage.wf _ WellFoundedRelation.wf
  subrelation {it it'} h := by
    simp_wf
    obtain ⟨step, h, h'⟩ := h
    cases step
    · cases h
      obtain ⟨_, h1, h2, _⟩ := h'
      have h3 := Pos.offset_prev_lt_offset (h := h1)
      simp [Pos.ext_iff, String.Pos.Raw.ext_iff, String.Pos.Raw.lt_iff] at h2 h3
      omega
    · cases h'
    · cases h

instance : Std.Iterators.Finite (BackwardCharPredSearcher s) Id :=
  .of_finitenessRelation finitenessRelation

instance : Std.IteratorLoop (BackwardCharPredSearcher s) Id Id :=
  .defaultImplementation

@[default_instance]
instance {p : Char → Bool} : ToBackwardSearcher p BackwardCharPredSearcher where
  toSearcher := iter p

@[default_instance]
instance {p : Char → Bool} : BackwardPattern p := ToBackwardSearcher.defaultImplementation

instance {p : Char → Prop} [DecidablePred p] : ToBackwardSearcher p BackwardCharPredSearcher where
  toSearcher := iter (decide <| p ·)

instance {p : Char → Prop} [DecidablePred p] : BackwardPattern p :=
  ToBackwardSearcher.defaultImplementation

end BackwardCharPredSearcher

end String.Slice.Pattern
