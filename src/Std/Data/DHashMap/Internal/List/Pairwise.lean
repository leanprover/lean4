/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
prelude
import Std.Data.DHashMap.Internal.List.Defs
import Std.Data.DHashMap.Internal.List.Perm
import Std.Data.DHashMap.Internal.List.Sublist

/-!
This is an internal implementation file of the hash map. Users of the hash map should not rely on
the contents of this file.

File contents: tiny private implementation of `List.Pairwise`
-/

namespace Std.DHashMap.Internal.List

set_option autoImplicit false

universe u

variable {α : Type u}

@[simp]
theorem Pairwise.nil {P : α → α → Prop} : Pairwise P [] :=
  trivial

theorem Pairwise.perm {P : α → α → Prop} (hP : ∀ {x y}, P x y → P y x) {l l' : List α}
    (h : Perm l l') : Pairwise P l → Pairwise P l' := by
  induction h
  · exact id
  · next l₁ l₂ a h ih => exact fun hx => ⟨fun y hy => hx.1 _ (h.mem_iff.2 hy), ih hx.2⟩
  · next l₁ _ a a' _ _ =>
    intro ⟨hx₁, hx₂, hx⟩
    refine ⟨?_, ?_, hx⟩
    · intro y hy
      rcases List.mem_cons.1 hy with rfl|hy
      · exact hP (hx₁ _ (List.mem_cons_self _ _))
      · exact hx₂ _ hy
    · exact fun y hy => hx₁ _ (List.mem_cons_of_mem _ hy)
  · next ih₁ ih₂ => exact ih₂ ∘ ih₁

theorem Pairwise.sublist {P : α → α → Prop} {l l' : List α} (h : Sublist l l') :
    Pairwise P l' → Pairwise P l := by
  induction h
  · exact id
  · next a l₁ l₂ h ih =>
    intro ⟨hx₁, hx⟩
    exact ⟨fun y hy => hx₁ _ (h.mem hy), ih hx⟩
  · next a l₁ l₂ _ ih =>
    intro ⟨_, hx⟩
    exact ih hx

theorem pairwise_cons {P : α → α → Prop} {a : α} {l : List α} :
    Pairwise P (a::l) ↔ (∀ y ∈ l, P a y) ∧ Pairwise P l :=
  Iff.rfl

end Std.DHashMap.Internal.List
