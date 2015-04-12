/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: data.finset
Author: Leonardo de Moura

Combinators for finite sets
-/
import data.finset.basic logic.identities
open list quot subtype decidable perm function

namespace finset
section map
variables {A B : Type}
variable [h : decidable_eq B]
include h

definition map (f : A → B) (s : finset A) : finset B :=
quot.lift_on s
  (λ l, to_finset (list.map f (elt_of l)))
  (λ l₁ l₂ p, quot.sound (perm_erase_dup_of_perm (perm_map _ p)))

theorem map_empty (f : A → B) : map f ∅ = ∅ :=
rfl
end map

section all
variables {A : Type}
definition all (s : finset A) (p : A → Prop) : Prop :=
quot.lift_on s
  (λ l, all (elt_of l) p)
  (λ l₁ l₂ p, foldr_eq_of_perm (λ a₁ a₂ q, propext !and.left_comm) p true)

theorem all_empty (p : A → Prop) : all ∅ p = true :=
rfl

theorem of_mem_of_all {p : A → Prop} {a : A} {s : finset A} : a ∈ s → all s p → p a :=
quot.induction_on s (λ l i h, list.of_mem_of_all i h)

theorem all_implies {p q : A → Prop} {s : finset A} : all s p → (∀ x, p x → q x) → all s q :=
quot.induction_on s (λ l h₁ h₂, list.all_implies h₁ h₂)

variable [h : decidable_eq A]
include h

theorem all_union {p : A → Prop} {s₁ s₂ : finset A} :  all s₁ p → all s₂ p → all (s₁ ∪ s₂) p :=
quot.induction_on₂ s₁ s₂ (λ l₁ l₂ a₁ a₂, all_union a₁ a₂)

theorem all_of_all_union_left {p : A → Prop} {s₁ s₂ : finset A} : all (s₁ ∪ s₂) p → all s₁ p :=
quot.induction_on₂ s₁ s₂ (λ l₁ l₂ a, list.all_of_all_union_left a)

theorem all_of_all_union_right {p : A → Prop} {s₁ s₂ : finset A} : all (s₁ ∪ s₂) p → all s₂ p :=
quot.induction_on₂ s₁ s₂ (λ l₁ l₂ a, list.all_of_all_union_right a)

theorem all_insert_of_all {p : A → Prop} {a : A} {s : finset A} : p a → all s p → all (insert a s) p :=
quot.induction_on s (λ l h₁ h₂, list.all_insert_of_all h₁ h₂)

theorem all_erase_of_all {p : A → Prop} (a : A) {s : finset A}: all s p → all (erase a s) p :=
quot.induction_on s (λ l h, list.all_erase_of_all a h)

theorem all_intersection_of_all_left {p : A → Prop} {s₁ : finset A} (s₂ : finset A) : all s₁ p → all (s₁ ∩ s₂) p :=
quot.induction_on₂ s₁ s₂ (λ l₁ l₂ h, list.all_intersection_of_all_left _ h)

theorem all_intersection_of_all_right {p : A → Prop} {s₁ : finset A} (s₂ : finset A) : all s₂ p → all (s₁ ∩ s₂) p :=
quot.induction_on₂ s₁ s₂ (λ l₁ l₂ h, list.all_intersection_of_all_right _ h)
end all

section cross_product
variables {A B : Type}
definition cross_product (s₁ : finset A) (s₂ : finset B) : finset (A × B) :=
quot.lift_on₂ s₁ s₂
  (λ l₁ l₂,
    to_finset_of_nodup (list.cross_product (elt_of l₁) (elt_of l₂))
                       (nodup_cross_product (has_property l₁) (has_property l₂)))
  (λ v₁ v₂ w₁ w₂ p₁ p₂, quot.sound (perm_cross_product p₁ p₂))

infix * := cross_product

theorem empty_cross_product (s : finset B) : @empty A * s = ∅ :=
quot.induction_on s (λ l, rfl)

theorem mem_cross_product {a : A} {b : B} {s₁ : finset A} {s₂ : finset B}
        : a ∈ s₁ → b ∈ s₂ → (a, b) ∈ s₁ * s₂ :=
quot.induction_on₂ s₁ s₂ (λ l₁ l₂ i₁ i₂, list.mem_cross_product i₁ i₂)

theorem mem_of_mem_cross_product_left {a : A} {b : B} {s₁ : finset A} {s₂ : finset B}
        : (a, b) ∈ s₁ * s₂ → a ∈ s₁ :=
quot.induction_on₂ s₁ s₂ (λ l₁ l₂ i, list.mem_of_mem_cross_product_left i)

theorem mem_of_mem_cross_product_right {a : A} {b : B} {s₁ : finset A} {s₂ : finset B}
        : (a, b) ∈ s₁ * s₂ → b ∈ s₂ :=
quot.induction_on₂ s₁ s₂ (λ l₁ l₂ i, list.mem_of_mem_cross_product_right i)

theorem cross_product_empty (s : finset A) : s * @empty B = ∅ :=
ext (λ p,
  match p with
  | (a, b) := iff.intro
     (λ i, absurd (mem_of_mem_cross_product_right i) !not_mem_empty)
     (λ i, absurd i !not_mem_empty)
  end)
end cross_product
end finset
