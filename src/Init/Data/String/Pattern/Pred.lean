/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving, Markus Himmel
-/
module

prelude
public import Init.Data.String.Pattern.Basic
public import Init.Data.Iterators.Consumers.Monadic.Loop
import Init.Data.String.Termination
public import Init.Data.String.Lemmas.IsEmpty
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

@[default_instance]
instance {p : Char → Bool} : BackwardPattern p where
  dropSuffixOfNonempty? s h :=
    if p ((s.endPos.prev (Ne.symm (by exact Slice.startPos_ne_endPos h))).get (by simp)) then
      some (s.endPos.prev (Ne.symm (by exact Slice.startPos_ne_endPos h)))
    else
      none
  dropSuffix? s :=
    if h : s.endPos = s.startPos then
      none
    else if p ((s.endPos.prev h).get (by simp)) then
      some (s.endPos.prev h)
    else
      none
  endsWith s :=
    if h : s.endPos = s.startPos then
      false
    else
      p ((s.endPos.prev h).get (by simp))

instance {p : Char → Bool} : StrictBackwardPattern p where
  ne_endPos {s h q} := by
    simp only [BackwardPattern.dropSuffixOfNonempty?, Option.ite_none_right_eq_some,
      Option.some.injEq, ne_eq, and_imp]
    rintro _ rfl
    simp

instance {p : Char → Bool} : LawfulBackwardPattern p where
  dropSuffixOfNonempty?_eq {s h} := by
    simp [BackwardPattern.dropSuffixOfNonempty?, BackwardPattern.dropSuffix?,
      Eq.comm (a := s.endPos), Slice.startPos_eq_endPos_iff, h]
  endsWith_eq {s} := by
    simp only [BackwardPattern.endsWith, BackwardPattern.dropSuffix?]
    split <;> (try split) <;> simp_all

@[default_instance]
instance {p : Char → Bool} : ToBackwardSearcher p (ToBackwardSearcher.DefaultBackwardSearcher p) :=
  .defaultImplementation

instance {p : Char → Prop} [DecidablePred p] : BackwardPattern p where
  dropSuffixOfNonempty? s h := BackwardPattern.dropSuffixOfNonempty? (decide <| p ·) s h
  dropSuffix? s := BackwardPattern.dropSuffix? (decide <| p ·) s
  endsWith s := BackwardPattern.endsWith (decide <| p ·) s

instance {p : Char → Prop} [DecidablePred p] : StrictBackwardPattern p where
  ne_endPos h q := StrictBackwardPattern.ne_endPos (pat := (decide <| p ·)) h q

instance {p : Char → Prop} [DecidablePred p] : LawfulBackwardPattern p where
  dropSuffixOfNonempty?_eq h := LawfulBackwardPattern.dropSuffixOfNonempty?_eq (pat := (decide <| p ·)) h
  endsWith_eq s := LawfulBackwardPattern.endsWith_eq (pat := (decide <| p ·)) s

instance {p : Char → Prop} [DecidablePred p] : ToBackwardSearcher p (ToBackwardSearcher.DefaultBackwardSearcher p) :=
  .defaultImplementation

end CharPred

end String.Slice.Pattern
