/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving, Markus Himmel
-/
module

prelude
public import Init.Data.String.Basic
public import Init.Data.Iterators.Consumers.Monadic.Loop
public import Init.Data.String.Iter
import Init.Data.Iterators.Combinators.FilterMap
import Init.Data.String.Termination

set_option doc.verso true

public section

namespace String.Slice

structure PosIterator (s : Slice) where
  currPos : s.Pos
deriving Inhabited

set_option doc.verso false
/--
Creates an iterator over all valid positions within {name}`s`.
Examples
 * {lean}`("abc".toSlice.positions.map (fun ⟨p, h⟩ => p.get h) |>.toList) = ['a', 'b', 'c']`
 * {lean}`("abc".toSlice.positions.map (·.val.offset.byteIdx) |>.toList) = [0, 1, 2]`
 * {lean}`("ab∀c".toSlice.positions.map (fun ⟨p, h⟩ => p.get h) |>.toList) = ['a', 'b', '∀', 'c']`
 * {lean}`("ab∀c".toSlice.positions.map (·.val.offset.byteIdx) |>.toList) = [0, 1, 2, 5]`
-/
def positions (s : Slice) : Std.Iter (α := PosIterator s) { p : s.Pos // p ≠ s.endPos } :=
  { internalState := { currPos := s.startPos }}

set_option doc.verso true

namespace PosIterator

instance : Std.Iterator (PosIterator s) Id { p : s.Pos // p ≠ s.endPos } where
  IsPlausibleStep it
    | .yield it' out =>
      ∃ h : it.internalState.currPos ≠ s.endPos,
        it'.internalState.currPos = it.internalState.currPos.next h ∧
        it.internalState.currPos = out
    | .skip _ => False
    | .done => it.internalState.currPos = s.endPos
  step := fun ⟨⟨currPos⟩⟩ =>
    if h : currPos = s.endPos then
      pure (.deflate ⟨.done, by simp [h]⟩)
    else
      pure (.deflate ⟨.yield ⟨⟨currPos.next h⟩⟩ ⟨currPos, h⟩, by simp [h]⟩)

private def finitenessRelation :
    Std.Iterators.FinitenessRelation (PosIterator s) Id where
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

@[no_expose]
instance : Std.Iterators.Finite (PosIterator s) Id :=
  .of_finitenessRelation finitenessRelation

instance : Std.IteratorLoop (PosIterator s) Id Id :=
  .defaultImplementation

docs_to_verso positions

end PosIterator

structure RevPosIterator (s : Slice) where
  currPos : s.Pos
deriving Inhabited

set_option doc.verso false
/--
Creates an iterator over all valid positions within {name}`s`, starting from the last valid
position and iterating towards the first one.
Examples
 * {lean}`("abc".toSlice.revPositions.map (fun ⟨p, h⟩ => p.get h) |>.toList) = ['c', 'b', 'a']`
 * {lean}`("abc".toSlice.revPositions.map (·.val.offset.byteIdx) |>.toList) = [2, 1, 0]`
 * {lean}`("ab∀c".toSlice.revPositions.map (fun ⟨p, h⟩ => p.get h) |>.toList) = ['c', '∀', 'b', 'a']`
 * {lean}`("ab∀c".toSlice.revPositions.map (·.val.offset.byteIdx) |>.toList) = [5, 2, 1, 0]`
-/
def revPositions (s : Slice) : Std.Iter (α := RevPosIterator s) { p : s.Pos // p ≠ s.endPos } :=
  { internalState := { currPos := s.endPos }}

set_option doc.verso true

namespace RevPosIterator

instance [Pure m] :
    Std.Iterator (RevPosIterator s) m { p : s.Pos // p ≠ s.endPos } where
  IsPlausibleStep it
    | .yield it' out =>
      ∃ h : it.internalState.currPos ≠ s.startPos,
        it'.internalState.currPos = it.internalState.currPos.prev h ∧
        it.internalState.currPos.prev h = out
    | .skip _ => False
    | .done => it.internalState.currPos = s.startPos
  step := fun ⟨⟨currPos⟩⟩ =>
    if h : currPos = s.startPos then
      pure (.deflate ⟨.done, by simp [h]⟩)
    else
      let prevPos := currPos.prev h
      pure (.deflate ⟨.yield ⟨⟨prevPos⟩⟩ ⟨prevPos, Pos.prev_ne_endPos⟩, by simp [h, prevPos]⟩)

private def finitenessRelation [Pure m] :
    Std.Iterators.FinitenessRelation (RevPosIterator s) m where
  Rel := InvImage WellFoundedRelation.rel
      (fun it => it.internalState.currPos.down)
  wf := InvImage.wf _ WellFoundedRelation.wf
  subrelation {it it'} h := by
    simp_wf
    obtain ⟨step, h, h'⟩ := h
    cases step
    · cases h
      obtain ⟨h1, h2, _⟩ := h'
      simp [h2]
    · cases h'
    · cases h

@[no_expose]
instance [Pure m] : Std.Iterators.Finite (RevPosIterator s) m :=
  .of_finitenessRelation finitenessRelation

instance [Monad m] [Monad n] : Std.IteratorLoop (RevPosIterator s) m n :=
  .defaultImplementation

docs_to_verso revPositions

end RevPosIterator


end String.Slice
