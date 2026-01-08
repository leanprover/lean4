/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Order.Lemmas
public import Init.Data.Order.MinMaxOn

set_option doc.verso true
set_option linter.missingDocs true

namespace List

/--
Returns an element of the non-empty list {name}`l` that minimizes {name}`f`. If {given}`x, y` are
such that {lean}`f x = f y`, it returns whichever comes first in the list.
-/
@[inline, suggest_for List.argmin]
public protected def minOn [LE β] [DecidableLE β] (f : α → β) (l : List α) (h : l ≠ []) : α :=
  match l with
  | x :: xs => xs.foldl (init := x) (minOn f)

/--
Returns an element of the non-empty list {name}`l` that maximizes {name}`f`. If {given}`x, y` are
such that {lean}`f x = f y`, it returns whichever comes first in the list.
-/
@[inline, suggest_for List.argmax]
public protected def maxOn [LE β] [DecidableLE β] (f : α → β) (l : List α) (h : l ≠ []) : α :=
  match l with
  | x :: xs => xs.foldl (init := x) (maxOn f)

/--
Returns an element of {name}`l` that minimizes {name}`f`. If {given}`x, y` are such that
{lean}`f x = f y`, it returns whichever comes first in the list. Returns {name}`none` if the list is
empty.
-/
@[inline, suggest_for List.argmin? List.argmin] -- Mathlib's `List.argmin` returns an `Option α`
public protected def minOn? [LE β] [DecidableLE β] (f : α → β) (l : List α) : Option α :=
  match l with
  | [] => none
  | x :: xs => some (xs.foldl (init := x) (minOn f))

/--
Returns an element of {name}`l` that maximizes {name}`f`. If {given}`x, y` are such that
{lean}`f x = f y`, it returns whichever comes first in the list. Returns {name}`none` if the list is
empty.
-/
@[inline, suggest_for List.argmax? List.argmax] -- Mathlib's `List.argmax` returns an `Option α`
public protected def maxOn? [LE β] [DecidableLE β] (f : α → β) (l : List α) : Option α :=
  match l with
  | [] => none
  | x :: xs => some (xs.foldl (init := x) (maxOn f))

@[grind =]
theorem maxOn_singleton [LE β] [DecidableLE β] {x : α} {f : α → β} :
    [x].maxOn f (of_decide_eq_false rfl) = x := by
  simp [List.maxOn]

@[grind =]
theorem argmax_assoc [LE β] [DecidableLE β] [IsLinearPreorder β] {f : α → β} {x y z : α} :
    argmax f (argmax f x y) z = argmax f x (argmax f y z) := by
  grind [argmax]

instance [LE β] [DecidableLE β] [IsLinearPreorder β] {f : α → β} :
    Associative (argmax f) where
  assoc := by apply argmax_assoc

theorem List.argmax_cons
    [LE β] [DecidableLE β] [IsLinearPreorder β] {x : α} {xs : List α} {f : α → β} :
    (x :: xs).argmax f (by grind) =
      if h : xs = [] then x else _root_.argmax f x (xs.argmax f h) := by
  simp only [argmax]
  match xs with
  | [] => simp
  | y :: xs => simp [foldl_assoc]

end List
