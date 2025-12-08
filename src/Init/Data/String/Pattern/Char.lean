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

instance (s : Slice) : Std.Iterators.Iterator (ForwardCharSearcher c s) Id (SearchStep s) where
  step
    | ⟨⟨currPos⟩⟩ => do
      if h1 : currPos = s.endPos then
        return .done
      else
        let nextPos := currPos.next h1
        let nextIt := ⟨⟨nextPos⟩⟩
        if currPos.get h1 = c then
          return .yield nextIt (.matched currPos nextPos)
        else
          return .yield nextIt (.rejected currPos nextPos)

def finitenessRelation : Std.Iterators.FinitenessRelation (ForwardCharSearcher s c) Id where
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

instance : Std.Iterators.Finite (ForwardCharSearcher s c) Id :=
  .of_finitenessRelation finitenessRelation

instance : Std.Iterators.IteratorLoop (ForwardCharSearcher s c) Id Id :=
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

instance (s : Slice) : Std.Iterators.Iterator (BackwardCharSearcher s) Id (SearchStep s) where
  step
    | ⟨currPos, needle⟩ => do
      if h1 : currPos = s.startPos then
        return .done
      else
        let nextPos := currPos.prev h1
        let nextIt := ⟨nextPos, needle⟩
        if nextPos.get Pos.prev_ne_endPos = needle then
          return .yield nextIt (.matched nextPos currPos)
        else
          return .yield nextIt (.rejected nextPos currPos)

def finitenessRelation : Std.Iterators.FinitenessRelation (BackwardCharSearcher s) Id where
  rel := InvImage WellFoundedRelation.rel (fun it => it.internalState.currPos.down)
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

instance : Std.Iterators.Finite (BackwardCharSearcher s) Id :=
  .of_finitenessRelation finitenessRelation

instance : Std.Iterators.IteratorLoop (BackwardCharSearcher s) Id Id :=
  .defaultImplementation

instance {c : Char} : ToBackwardSearcher c BackwardCharSearcher where
  toSearcher := iter c

instance {c : Char} : BackwardPattern c := ToBackwardSearcher.defaultImplementation

end BackwardCharSearcher

end String.Slice.Pattern
