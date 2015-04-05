/-
copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LIcENSE.

Module: data.set.basic
Author: Jeremy Avigad, Leonardo de Moura
-/
import logic
open eq.ops

definition set (T : Type) := T → Prop

namespace set

variable {T : Type}

definition mem [reducible] (x : T) (a : set T) := a x
notation e ∈ a := mem e a

theorem setext {a b : set T} (H : ∀x, x ∈ a ↔ x ∈ b) : a = b :=
funext (take x, propext (H x))

definition subset (a b : set T) := ∀ x, x ∈ a → x ∈ b
infix `⊆`:50 := subset

definition eq_of_subset_of_subset (a b : set T) (H₁ : a ⊆ b) (H₂ : b ⊆ a) : a = b :=
setext (take x, iff.intro (H₁ x) (H₂ x))

/- empty -/

definition empty [reducible] : set T := λx, false
notation `∅` := empty

theorem mem_empty (x : T) : ¬ (x ∈ ∅) :=
assume H : x ∈ ∅, H

/- univ -/

definition univ : set T := λx, true

theorem mem_univ (x : T) : x ∈ univ := trivial

/- inter -/

definition inter [reducible] (a b : set T) : set T := λx, x ∈ a ∧ x ∈ b
notation a ∩ b := inter a b

theorem mem_inter (x : T) (a b : set T) : x ∈ a ∩ b ↔ (x ∈ a ∧ x ∈ b) := !iff.refl

theorem inter_self (a : set T) : a ∩ a = a :=
setext (take x, iff.intro
  (assume H, and.elim_left H)
  (assume H, and.intro H H))

theorem inter_empty (a : set T) : a ∩ ∅ = ∅ :=
setext (take x, iff.intro
  (assume H, and.elim_right H)
  (assume H, false.elim H))

theorem empty_inter (a : set T) : ∅ ∩ a = ∅ :=
setext (take x, iff.intro
  (assume H, and.elim_left H)
  (assume H, false.elim H))

theorem inter.comm (a b : set T) : a ∩ b = b ∩ a :=
setext (take x, !and.comm)

theorem inter.assoc (a b c : set T) : (a ∩ b) ∩ c = a ∩ (b ∩ c) :=
setext (take x, !and.assoc)

/- union -/

definition union [reducible] (a b : set T) : set T := λx, x ∈ a ∨ x ∈ b
notation a ∪ b := union a b

theorem mem_union (x : T) (a b : set T) : x ∈ a ∪ b ↔ (x ∈ a ∨ x ∈ b) := !iff.refl

theorem union_self (a : set T) : a ∪ a = a :=
setext (take x, iff.intro
  (assume H,
    match H with
    | or.inl H₁ := H₁
    | or.inr H₂ := H₂
    end)
  (assume H, or.inl H))

theorem union_empty (a : set T) : a ∪ ∅ = a :=
setext (take x, iff.intro
  (assume H, match H with
             | or.inl H₁ := H₁
             | or.inr H₂ := false.elim H₂
             end)
  (assume H, or.inl H))

theorem union_empty_left (a : set T) : ∅ ∪ a = a :=
setext (take x, iff.intro
  (assume H, match H with
             | or.inl H₁ := false.elim H₁
             | or.inr H₂ := H₂
             end)
  (assume H, or.inr H))

theorem union.comm (a b : set T) : a ∪ b = b ∪ a :=
setext (take x, or.comm)

theorem union_assoc (a b c : set T) : (a ∪ b) ∪ c = a ∪ (b ∪ c) :=
setext (take x, or.assoc)

end set
