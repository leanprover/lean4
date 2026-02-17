/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving, Markus Himmel
-/
module

prelude
public import Init.Data.String.Pattern.Basic
import Init.Data.String.Lemmas.FindPos
import Init.Data.String.Termination
import Init.Data.String.Lemmas.IsEmpty
import Init.Data.String.Lemmas.Order
import Init.Data.Option.Lemmas

set_option doc.verso true

/-!
This module defines the necessary instances to register {name}`Char` with the pattern framework.
-/

public section

namespace String.Slice.Pattern

namespace Char

instance {c : Char} : ForwardPattern c where
  dropPrefixOfNonempty? s h :=
    if s.startPos.get (by exact Slice.startPos_ne_endPos h) = c then
      some (s.startPos.next (by exact Slice.startPos_ne_endPos h))
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

instance {c : Char} : ToForwardSearcher c (ToForwardSearcher.DefaultForwardSearcher c) :=
  .defaultImplementation

instance {c : Char} : BackwardPattern c where
  dropSuffixOfNonempty? s h :=
    if (s.endPos.prev (Ne.symm (by exact Slice.startPos_ne_endPos h))).get (by simp) = c then
      some (s.endPos.prev (Ne.symm (by exact Slice.startPos_ne_endPos h)))
    else
      none
  dropSuffix? s :=
    if h : s.endPos = s.startPos then
      none
    else if (s.endPos.prev h).get (by simp) = c then
      some (s.endPos.prev h)
    else
      none
  endsWith s :=
    if h : s.endPos = s.startPos then
      false
    else
      (s.endPos.prev h).get (by simp) = c

instance {c : Char} : StrictBackwardPattern c where
  ne_endPos {s h q} := by
    simp only [BackwardPattern.dropSuffixOfNonempty?, Option.ite_none_right_eq_some,
      Option.some.injEq, ne_eq, and_imp]
    rintro _ rfl
    simp

instance {c : Char} : LawfulBackwardPattern c where
  dropSuffixOfNonempty?_eq {s h} := by
    simp [BackwardPattern.dropSuffixOfNonempty?, BackwardPattern.dropSuffix?,
      Eq.comm (a := s.endPos), Slice.startPos_eq_endPos_iff, h]
  endsWith_eq {s} := by
    simp only [BackwardPattern.endsWith, BackwardPattern.dropSuffix?]
    split <;> (try split) <;> simp_all

instance {c : Char} : ToBackwardSearcher c (ToBackwardSearcher.DefaultBackwardSearcher c) :=
  .defaultImplementation

end Char

end String.Slice.Pattern
