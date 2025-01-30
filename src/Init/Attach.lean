/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/

prelude

import Init.WF
import Init.Data.List.Attach
import Init.Data.Array.Attach

theorem List.wfParam_to_attach (xs : List α) :
    (wfParam xs) = xs.attach.unattach :=
  List.unattach_attach.symm

theorem Array.wfParam_to_attach (xs : Array α) :
    (wfParam xs) = xs.attach.unattach :=
  Array.unattach_attach.symm

set_option linter.unusedVariables false in
theorem List.map_unattach (P : α → Prop) (xs : List (Subtype P)) (f : α → β) :
    xs.unattach.map f = xs.map (fun ⟨x, h⟩ => f (wfParam x)) := by
  simp [wfParam]

set_option linter.unusedVariables false in
theorem List.filter_unattach (P : α → Prop) (xs : List (Subtype P)) (f : α → Bool) :
    xs.unattach.filter f = (xs.filter (fun ⟨x, h⟩ => f (wfParam x))).unattach := by
  simp [wfParam]

theorem List.reverse_unattach (P : α → Prop) (xs : List (Subtype P)) :
    xs.unattach.reverse = xs.reverse.unattach := by simp

set_option linter.unusedVariables false in
theorem Array.map_unattach (P : α → Prop) (xs : Array (Subtype P)) (f : α → β) :
    xs.unattach.map f = xs.map (fun ⟨x, h⟩ => f (wfParam x)) := by
  simp [wfParam]
