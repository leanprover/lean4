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

instance (s : Slice) : Std.Iterators.Iterator (ForwardCharPredSearcher p s) Id (SearchStep s) where
  step := fun ⟨⟨currPos⟩⟩ => do
    if h1 : currPos = s.endPos then
      return .done
    else
      let nextPos := currPos.next h1
      let nextIt := ⟨⟨nextPos⟩⟩
      if p <| currPos.get h1 then
        return .yield nextIt (.matched currPos nextPos)
      else
        return .yield nextIt (.rejected currPos nextPos)


def finitenessRelation : Std.Iterators.FinitenessRelation (ForwardCharPredSearcher p s) Id where
  rel := InvImage WellFoundedRelation.rel (fun it => it.internalState.currPos)
  wf := InvImage.wf _ WellFoundedRelation.wf
  subrelation {it it'} h := by
    simp_wf
    obtain ⟨step, h, h'⟩ := h
    simp only [Std.Iterators.IterM.IsPlausibleStep, MonadAttach.CanReturn,
      Std.Iterators.Iterator.step] at h'
    split at h'
    · cases h'
      cases h
    · split at h' <;> (cases h'; cases h; simp)
    simp_wf

instance : Std.Iterators.Finite (ForwardCharPredSearcher p s) Id :=
  .of_finitenessRelation finitenessRelation

instance : Std.Iterators.IteratorLoop (ForwardCharPredSearcher p s) Id Id :=
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

instance (s : Slice) : Std.Iterators.Iterator (BackwardCharPredSearcher s) Id (SearchStep s) where
  step := fun ⟨currPos, needle⟩ => do
    if h1 : currPos = s.startPos then
      return .done
    else
      let nextPos := currPos.prev h1
      let nextIt := ⟨nextPos, needle⟩
      if needle <| nextPos.get Pos.prev_ne_endPos then
        return .yield nextIt (.matched nextPos currPos)
      else
        return .yield nextIt (.rejected nextPos currPos)

def finitenessRelation : Std.Iterators.FinitenessRelation (BackwardCharPredSearcher s) Id where
  rel := InvImage WellFoundedRelation.rel
      (fun it => it.internalState.currPos.offset.byteIdx)
  wf := InvImage.wf _ WellFoundedRelation.wf
  subrelation {it it'} h := by
    simp_wf
    obtain ⟨step, h, h'⟩ := h
    simp only [Std.Iterators.IterM.IsPlausibleStep, MonadAttach.CanReturn,
      Std.Iterators.Iterator.step] at h'
    split at h'
    · cases h'
      cases h
    · cases h'
      have h3 := Pos.offset_prev_lt_offset (h := ‹_›)
      split at h <;> (cases h; simpa using h3)

instance : Std.Iterators.Finite (BackwardCharPredSearcher s) Id :=
  .of_finitenessRelation finitenessRelation

instance : Std.Iterators.IteratorLoop (BackwardCharPredSearcher s) Id Id :=
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
