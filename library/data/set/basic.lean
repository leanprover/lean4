/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: data.set.basic
Author: Jeremy Avigad, Leonardo de Moura
-/
import logic
open eq.ops

namespace set
definition set (T : Type) :=
T → Prop
definition mem [reducible] {T : Type} (x : T) (s : set T) :=
s x
notation e ∈ s := mem e s

variable {T : Type}
definition eqv (A B : set T) : Prop :=
∀x, x ∈ A ↔ x ∈ B
notation a ∼ b := eqv a b

theorem eqv_refl (A : set T) : A ∼ A :=
take x, iff.rfl

theorem eqv_symm {A B : set T} (H : A ∼ B) : B ∼ A :=
take x, iff.symm (H x)

theorem eqv_trans {A B C : set T} (H1 : A ∼ B) (H2 : B ∼ C) : A ∼ C :=
take x, iff.trans (H1 x) (H2 x)

definition empty [reducible] : set T :=
λx, false
notation `∅` := empty

theorem mem_empty (x : T) : ¬ (x ∈ ∅) :=
assume H : x ∈ ∅, H

definition univ : set T :=
λx, true

theorem mem_univ (x : T) : x ∈ univ :=
trivial

definition inter [reducible] (A B : set T) : set T :=
λx, x ∈ A ∧ x ∈ B
notation a ∩ b := inter a b

theorem mem_inter (x : T) (A B : set T) : x ∈ A ∩ B ↔ (x ∈ A ∧ x ∈ B) :=
!iff.refl

theorem inter_id (A : set T) : A ∩ A ∼ A :=
take x, iff.intro
  (assume H, and.elim_left H)
  (assume H, and.intro H H)

theorem inter_empty_right (A : set T) : A ∩ ∅ ∼ ∅ :=
take x, iff.intro
  (assume H, and.elim_right H)
  (assume H, false.elim H)

theorem inter_empty_left (A : set T) : ∅ ∩ A ∼ ∅ :=
take x, iff.intro
  (assume H, and.elim_left H)
  (assume H, false.elim H)

theorem inter_comm (A B : set T) : A ∩ B ∼ B ∩ A :=
take x, !and.comm

theorem inter_assoc (A B C : set T) : (A ∩ B) ∩ C ∼ A ∩ (B ∩ C) :=
take x, !and.assoc

definition union [reducible] (A B : set T) : set T :=
λx, x ∈ A ∨ x ∈ B
notation a ∪ b := union a b

theorem mem_union (x : T) (A B : set T) : x ∈ A ∪ B ↔ (x ∈ A ∨ x ∈ B) :=
!iff.refl

theorem union_id (A : set T) : A ∪ A ∼ A :=
take x, iff.intro
  (assume H,
    match H with
    | or.inl H₁ := H₁
    | or.inr H₂ := H₂
    end)
  (assume H, or.inl H)

theorem union_empty_right (A : set T) : A ∪ ∅ ∼ A :=
take x, iff.intro
  (assume H, match H with
             | or.inl H₁ := H₁
             | or.inr H₂ := false.elim H₂
             end)
  (assume H, or.inl H)

theorem union_empty_left (A : set T) : ∅ ∪ A ∼ A :=
take x, iff.intro
  (assume H, match H with
             | or.inl H₁ := false.elim H₁
             | or.inr H₂ := H₂
             end)
  (assume H, or.inr H)

theorem union_comm (A B : set T) : A ∪ B ∼ B ∪ A :=
take x, or.comm

theorem union_assoc (A B C : set T) : (A ∪ B) ∪ C ∼ A ∪ (B ∪ C) :=
take x, or.assoc

definition subset (A B : set T) := ∀ x, x ∈ A → x ∈ B
infix `⊆`:50 := subset

definition eqv_of_subset (A B : set T) : A ⊆ B → B ⊆ A → A ∼ B :=
assume H₁ H₂, take x, iff.intro (H₁ x) (H₂ x)

end set
