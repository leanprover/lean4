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
This module defines the necessary instances to register {lean}`Char → Bool` with the pattern
framework.
-/

public section

namespace String.Slice.Pattern

namespace CharPred

@[default_instance]
instance {p : Char → Bool} : ForwardPattern p where
  dropPrefixOfNonempty? s h :=
    if p (s.startPos.get (Slice.startPos_ne_endPos h)) then
      some (s.startPos.next (Slice.startPos_ne_endPos h))
    else
      none
  dropPrefix? s :=
    if h : s.startPos = s.endPos then
      none
    else if p (s.startPos.get h) then
      some (s.startPos.next h)
    else
      none
  startsWith s :=
    if h : s.startPos = s.endPos then
      false
    else
      p (s.startPos.get h)

instance {p : Char → Bool} : StrictForwardPattern p where
  ne_startPos {s h q} := by
    simp only [ForwardPattern.dropPrefixOfNonempty?, Option.ite_none_right_eq_some,
      Option.some.injEq, ne_eq, and_imp]
    rintro _ rfl
    simp

instance {p : Char → Bool} : LawfulForwardPattern p where
  dropPrefixOfNonempty?_eq {s} h := by
    simp [ForwardPattern.dropPrefixOfNonempty?, ForwardPattern.dropPrefix?,
      Slice.startPos_eq_endPos_iff, h]
  startsWith_eq s := by
    simp only [ForwardPattern.startsWith, ForwardPattern.dropPrefix?]
    split <;> (try split) <;> simp_all

@[default_instance]
instance {p : Char → Bool} : ToForwardSearcher p (ToForwardSearcher.DefaultForwardSearcher p) :=
  .defaultImplementation

instance {p : Char → Prop} [DecidablePred p] : ForwardPattern p where
  dropPrefixOfNonempty? s h := ForwardPattern.dropPrefixOfNonempty? (decide <| p ·) s h
  dropPrefix? s := ForwardPattern.dropPrefix? (decide <| p ·) s
  startsWith s := ForwardPattern.startsWith (decide <| p ·) s

instance {p : Char → Prop} [DecidablePred p] : StrictForwardPattern p where
  ne_startPos h q := StrictForwardPattern.ne_startPos (pat := (decide <| p ·)) h q

instance {p : Char → Prop} [DecidablePred p] : LawfulForwardPattern p where
  dropPrefixOfNonempty?_eq h := LawfulForwardPattern.dropPrefixOfNonempty?_eq (pat := (decide <| p ·)) h
  startsWith_eq s := LawfulForwardPattern.startsWith_eq (pat := (decide <| p ·)) s

instance {p : Char → Prop} [DecidablePred p] : ToForwardSearcher p (ToForwardSearcher.DefaultForwardSearcher p) :=
  .defaultImplementation

end CharPred

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
