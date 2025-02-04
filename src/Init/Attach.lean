/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/

prelude

import Init.WF
import Init.Data.List.Attach
import Init.Data.Array.Attach
import Init.BinderNameHint

/-
At some point I tried to use this rule to upgrade `wfParam` to `….unattach` to only
have a single rule for each function below. But then there are `xs.attach.unattach` below that were
sometimes hard to reliably get rid of.

So for now I keep `wfParam`, and have duplicate rules below.
Maybe later I can create an attribute that takes the `xs.unattach`-rule and then produce the
alternative form from it (like Mathlib’s `assoc` attribute).

theorem List.wfParam_to_attach (xs : List α) :
    (wfParam xs) = xs.attach.unattach :=
  List.unattach_attach.symm

theorem Array.wfParam_to_attach (xs : Array α) :
    (wfParam xs) = xs.attach.unattach :=
  Array.unattach_attach.symm
-/

theorem List.map_wfParam (xs : List α) (f : α → β) :
    (wfParam xs).map f = xs.attach.unattach.map f := by
  simp [wfParam]

set_option linter.unusedVariables false in
theorem List.map_unattach (P : α → Prop) (xs : List (Subtype P)) (f : α → β) :
    xs.unattach.map f = xs.map (fun ⟨x, h⟩ => binderNameHint x f (f (wfParam x))) := by
  simp [wfParam]

theorem List.foldl_wfParam (xs : List α) (f : β → α → β) (init : β):
    (wfParam xs).foldl f init = xs.attach.unattach.foldl f init := by
  simp [wfParam]

set_option linter.unusedVariables false in
theorem List.foldl_unattach (P : α → Prop) (xs : List (Subtype P)) (f : β → α → β) (init : β):
    xs.unattach.foldl f init = xs.foldl (fun s ⟨x, h⟩ => binderNameHint x f (f s (wfParam x) )) init := by
  simp [wfParam]

-- TODO: Unused, here, but worth moving to library?
theorem List.unattach_foldl {p : α → Prop} {l : List { x // p x }}
    {f : β → { x // p x } → β} {g : β → α → β} {hf : ∀ s x h, f s ⟨x, h⟩ = g s x} :
    (l.foldl f) = l.unattach.foldl g := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp [foldl_cons, hf, List.unattach_cons]

theorem List.filter_wfParam (xs : List α) (f : α → Bool) :
    (wfParam xs).filter f = xs.attach.unattach.filter f:= by
  simp [wfParam]

set_option linter.unusedVariables false in
theorem List.filter_unattach (P : α → Prop) (xs : List (Subtype P)) (f : α → Bool) :
    xs.unattach.filter f = (xs.filter (fun ⟨x, h⟩ => binderNameHint x f (f (wfParam x)))).unattach := by
  simp [wfParam]

theorem List.reverse_wfParam (xs : List α) :
    (wfParam xs).reverse = xs.attach.unattach.reverse:= by simp [wfParam]

theorem List.reverse_unattach (P : α → Prop) (xs : List (Subtype P)) :
    xs.unattach.reverse = xs.reverse.unattach := by simp

theorem Array.map_wfParam (xs : Array α) (f : α → β) :
    (wfParam xs).map f = xs.attach.unattach.map f := by
  simp [wfParam]

set_option linter.unusedVariables false in
theorem Array.map_unattach (P : α → Prop) (xs : Array (Subtype P)) (f : α → β) :
    xs.unattach.map f = xs.map (fun ⟨x, h⟩ => binderNameHint x f (f (wfParam x))) := by
  simp [wfParam]
