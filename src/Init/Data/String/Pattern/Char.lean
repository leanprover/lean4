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
public import Init.Data.String.Lemmas.SliceIsEmpty
import Init.Data.String.Lemmas.Order

set_option doc.verso true

/-!
This module defines the necessary instances to register {name}`Char` with the pattern framework.
-/

public section

namespace String.Slice.Pattern

namespace Char

@[inline, always_inline]
instance {c : Char} : ForwardPattern c where
  dropPrefixOfNonempty? s h :=
    if s.startPos.get (Slice.startPos_ne_endPos h) = c then
      some (s.startPos.next (Slice.startPos_ne_endPos h))
    else
      none
  dropPrefix? s :=
    if h : s.startPos = s.endPos then
      none
    else if s.startPos.get h = c then
      some (s.startPos.next h)
    else
      none
  startsWith s :=
    if h : s.startPos = s.endPos then
      false
    else
      s.startPos.get h = c

instance {c : Char} : StrictForwardPattern c where
  ne_startPos {s h q} := by
    simp only [ForwardPattern.dropPrefixOfNonempty?, Option.ite_none_right_eq_some,
      Option.some.injEq, ne_eq, and_imp]
    rintro _ rfl
    simp

instance {c : Char} : LawfulForwardPattern c where
  dropPrefixOfNonempty?_eq {s h} := by
    simp [ForwardPattern.dropPrefixOfNonempty?, ForwardPattern.dropPrefix?,
      Slice.startPos_eq_endPos_iff, h]
  startsWith_eq {s} := by
    simp only [ForwardPattern.startsWith, ForwardPattern.dropPrefix?]
    split <;> (try split) <;> simp_all

@[inline, always_inline]
instance {c : Char} : ToForwardSearcher c (ToForwardSearcher.DefaultForwardSearcher c) :=
  .defaultImplementation

end Char

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
