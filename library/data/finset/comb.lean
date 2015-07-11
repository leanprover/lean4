/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura, Jeremy Avigad

Combinators for finite sets.
-/
import data.finset.basic logic.identities
open list quot subtype decidable perm function

namespace finset

/- image (corresponds to map on list) -/
section image
variables {A B : Type}
variable [h : decidable_eq B]
include h

definition image (f : A → B) (s : finset A) : finset B :=
quot.lift_on s
  (λ l, to_finset (list.map f (elt_of l)))
  (λ l₁ l₂ p, quot.sound (perm_erase_dup_of_perm (perm_map _ p)))

theorem image_empty (f : A → B) : image f ∅ = ∅ :=
rfl

theorem mem_image_of_mem (f : A → B) {s : finset A} {a : A} : a ∈ s → f a ∈ image f s :=
quot.induction_on s (take l, assume H : a ∈ elt_of l, mem_to_finset (mem_map f H))

theorem mem_image_of_mem_of_eq {f : A → B} {s : finset A} {a : A} {b : B}
    (H1 : a ∈ s) (H2 : f a = b) :
  b ∈ image f s :=
eq.subst H2 (mem_image_of_mem f H1)

theorem exists_of_mem_image {f : A → B} {s : finset A} {b : B} :
  b ∈ image f s → ∃a, a ∈ s ∧ f a = b :=
quot.induction_on s
  (take l, assume H : b ∈ erase_dup (list.map f (elt_of l)),
    exists_of_mem_map (mem_of_mem_erase_dup H))

theorem mem_image_iff (f : A → B) {s : finset A} {y : B} : y ∈ image f s ↔ ∃x, x ∈ s ∧ f x = y :=
iff.intro exists_of_mem_image
  (assume H,
    obtain x (H₁ : x ∈ s) (H₂ : f x = y), from H,
    mem_image_of_mem_of_eq H₁ H₂)

theorem mem_image_eq (f : A → B) {s : finset A} {y : B} : y ∈ image f s = ∃x, x ∈ s ∧ f x = y :=
propext (mem_image_iff f)

theorem mem_image_of_mem_image_of_subset {f : A → B} {s t : finset A} {y : B}
    (H1 : y ∈ image f s) (H2 : s ⊆ t) : y ∈ image f t :=
obtain x (H3: x ∈ s) (H4 : f x = y), from exists_of_mem_image H1,
have H5 : x ∈ t, from mem_of_subset_of_mem H2 H3,
show y ∈ image f t, from mem_image_of_mem_of_eq H5 H4

theorem image_insert [h' : decidable_eq A] (f : A → B) (s : finset A) (a : A) :
  image f (insert a s) = insert (f a) (image f s) :=
ext (take y, iff.intro
  (assume H : y ∈ image f (insert a s),
    obtain x (H1l : x ∈ insert a s) (H1r :f x = y), from exists_of_mem_image H,
    have H2 : x = a ∨ x ∈ s, from eq_or_mem_of_mem_insert H1l,
    or.elim H2
      (assume H3 : x = a,
        have H4 : f a = y, from eq.subst H3 H1r,
        show y ∈ insert (f a) (image f s), from eq.subst H4 !mem_insert)
      (assume H3 : x ∈ s,
        have H5 : f x ∈ image f s, from mem_image_of_mem f H3,
        show y ∈ insert (f a) (image f s), from eq.subst H1r (mem_insert_of_mem _ H5)))
  (assume H : y ∈ insert (f a) (image f s),
    have H1 : y = f a ∨ y ∈ image f s, from eq_or_mem_of_mem_insert H,
    or.elim H1
      (assume H2 : y = f a,
        have H3 : f a ∈ image f (insert a s), from mem_image_of_mem f !mem_insert,
        show y ∈ image f (insert a s), from eq.subst (eq.symm H2) H3)
      (assume H2 : y ∈ image f s,
        show y ∈ image f (insert a s), from mem_image_of_mem_image_of_subset H2 !subset_insert)))

lemma image_compose {C : Type} [deceqC : decidable_eq C] {f : B → C} {g : A → B} {s : finset A} :
  image (f∘g) s = image f (image g s) :=
ext (take z, iff.intro
  (assume Hz : z ∈ image (f∘g) s,
    obtain x (Hx : x ∈ s) (Hgfx : f (g x) = z), from exists_of_mem_image Hz,
    by rewrite -Hgfx; apply mem_image_of_mem _ (mem_image_of_mem _ Hx))
  (assume Hz : z ∈ image f (image g s),
    obtain y (Hy : y ∈ image g s) (Hfy : f y = z), from exists_of_mem_image Hz,
    obtain x (Hx : x ∈ s) (Hgx : g x = y), from exists_of_mem_image Hy,
    mem_image_of_mem_of_eq Hx (by esimp; rewrite [Hgx, Hfy])))

end image

/- filter and set-builder notation -/
section filter
variables {A : Type} [deceq : decidable_eq A]
include deceq
variables (p : A → Prop) [decp : decidable_pred p] (s : finset A) {x : A}
include decp

definition filter : finset A :=
quot.lift_on s
  (λl, to_finset_of_nodup
    (list.filter p (subtype.elt_of l))
    (list.nodup_filter p (subtype.has_property l)))
  (λ l₁ l₂ u, quot.sound (perm.perm_filter u))

notation `{` binders ∈ s `|` r:(scoped:1 p, filter p s) `}` := r

theorem filter_empty : filter p ∅ = ∅ := rfl

variables {p s}

theorem of_mem_filter : x ∈ filter p s → p x :=
quot.induction_on s (take l, list.of_mem_filter)

theorem mem_of_mem_filter : x ∈ filter p s → x ∈ s :=
quot.induction_on s (take l, list.mem_of_mem_filter)

theorem mem_filter_of_mem {x : A} : x ∈ s → p x → x ∈ filter p s :=
quot.induction_on s (take l, list.mem_filter_of_mem)

variables (p s)

theorem mem_filter_iff : x ∈ filter p s ↔ x ∈ s ∧ p x :=
iff.intro
  (assume H, and.intro (mem_of_mem_filter H) (of_mem_filter H))
  (assume H, mem_filter_of_mem (and.left H) (and.right H))

theorem mem_filter_eq : x ∈ filter p s = (x ∈ s ∧ p x) :=
propext !mem_filter_iff
end filter

/- set difference -/
section diff
variables {A : Type} [deceq : decidable_eq A]
include deceq

definition diff (s t : finset A) : finset A := {x ∈ s | x ∉ t}
infix `\`:70 := diff

theorem mem_of_mem_diff {s t : finset A} {x : A} (H : x ∈ s \ t) : x ∈ s :=
mem_of_mem_filter H

theorem not_mem_of_mem_diff {s t : finset A} {x : A} (H : x ∈ s \ t) : x ∉ t :=
of_mem_filter H

theorem mem_diff {s t : finset A} {x : A} (H1 : x ∈ s) (H2 : x ∉ t) : x ∈ s \ t :=
mem_filter_of_mem H1 H2

theorem mem_diff_iff (s t : finset A) (x : A) : x ∈ s \ t ↔ x ∈ s ∧ x ∉ t :=
iff.intro
  (assume H, and.intro (mem_of_mem_diff H) (not_mem_of_mem_diff H))
  (assume H, mem_diff (and.left H) (and.right H))

theorem mem_diff_eq (s t : finset A) (x : A) : x ∈ s \ t = (x ∈ s ∧ x ∉ t) :=
propext !mem_diff_iff

theorem union_diff_cancel {s t : finset A} (H : s ⊆ t) : s ∪ (t \ s) = t :=
ext (take x, iff.intro
  (assume H1 : x ∈ s ∪ (t \ s),
    or.elim (mem_or_mem_of_mem_union H1)
      (assume H2 : x ∈ s, mem_of_subset_of_mem H H2)
      (assume H2 : x ∈ t \ s, mem_of_mem_diff H2))
  (assume H1 : x ∈ t,
    decidable.by_cases
      (assume H2 : x ∈ s, mem_union_left _ H2)
      (assume H2 : x ∉ s, mem_union_right _ (mem_diff H1 H2))))

theorem diff_union_cancel {s t : finset A} (H : s ⊆ t) : (t \ s) ∪ s = t :=
eq.subst !union.comm (!union_diff_cancel H)
end diff

/- all -/
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

theorem forall_of_all {p : A → Prop} {s : finset A} (H : all s p) : ∀{a}, a ∈ s → p a :=
λ a H', of_mem_of_all H' H

theorem all_of_forall {p : A → Prop} {s : finset A} : (∀a, a ∈ s → p a) → all s p :=
quot.induction_on s (λ l H, list.all_of_forall H)

theorem all_iff_forall (p : A → Prop) (s : finset A) : all s p ↔ (∀a, a ∈ s → p a) :=
iff.intro forall_of_all all_of_forall

definition decidable_all [instance] (p : A → Prop) [h : decidable_pred p] (s : finset A) :
  decidable (all s p) :=
quot.rec_on_subsingleton s (λ l, list.decidable_all p (elt_of l))

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

theorem all_inter_of_all_left {p : A → Prop} {s₁ : finset A} (s₂ : finset A) : all s₁ p → all (s₁ ∩ s₂) p :=
quot.induction_on₂ s₁ s₂ (λ l₁ l₂ h, list.all_inter_of_all_left _ h)

theorem all_inter_of_all_right {p : A → Prop} {s₁ : finset A} (s₂ : finset A) : all s₂ p → all (s₁ ∩ s₂) p :=
quot.induction_on₂ s₁ s₂ (λ l₁ l₂ h, list.all_inter_of_all_right _ h)

theorem subset_iff_all (s t : finset A) : s ⊆ t ↔ all s (λ x, x ∈ t) :=
iff.intro
  (assume H : s ⊆ t, all_of_forall (take x, assume H1, mem_of_subset_of_mem H H1))
  (assume H : all s (λ x, x ∈ t), subset_of_forall (take x, assume H1 : x ∈ s, of_mem_of_all H1 H))

definition decidable_subset [instance] (s t : finset A) : decidable (s ⊆ t) :=
decidable_of_decidable_of_iff _ (iff.symm !subset_iff_all)
end all

/- any -/
section any
variables {A : Type}
definition any (s : finset A) (p : A → Prop) : Prop :=
quot.lift_on s
  (λ l, any (elt_of l) p)
  (λ l₁ l₂ p, foldr_eq_of_perm (λ a₁ a₂ q, propext !or.left_comm) p false)

theorem any_empty (p : A → Prop) : any ∅ p = false := rfl

theorem exists_of_any {p : A → Prop} {s : finset A} : any s p → ∃a, a ∈ s ∧ p a :=
quot.induction_on s (λ l H, list.exists_of_any H)

theorem any_of_mem {p : A → Prop} {s : finset A} {a : A} : a ∈ s → p a → any s p :=
quot.induction_on s (λ l H1 H2, list.any_of_mem H1 H2)

theorem any_of_exists {p : A → Prop} {s : finset A} (H : ∃a, a ∈ s ∧ p a) : any s p :=
obtain a H₁ H₂, from H,
any_of_mem H₁ H₂

theorem any_iff_exists (p : A → Prop) (s : finset A) : any s p ↔ (∃a, a ∈ s ∧ p a) :=
iff.intro exists_of_any any_of_exists

theorem any_of_insert [h : decidable_eq A] {p : A → Prop} (s : finset A) {a : A} (H : p a) :
  any (insert a s) p :=
any_of_mem (mem_insert a s) H

theorem any_of_insert_right [h : decidable_eq A] {p : A → Prop} {s : finset A} (a : A) (H : any s p) :
  any (insert a s) p :=
obtain b (H₁ : b ∈ s) (H₂ : p b), from exists_of_any H,
any_of_mem (mem_insert_of_mem a H₁) H₂

definition decidable_any [instance] (p : A → Prop) [h : decidable_pred p] (s : finset A) :
  decidable (any s p) :=
quot.rec_on_subsingleton s (λ l, list.decidable_any p (elt_of l))
end any

section product
variables {A B : Type}
definition product (s₁ : finset A) (s₂ : finset B) : finset (A × B) :=
quot.lift_on₂ s₁ s₂
  (λ l₁ l₂,
    to_finset_of_nodup (product (elt_of l₁) (elt_of l₂))
                       (nodup_product (has_property l₁) (has_property l₂)))
  (λ v₁ v₂ w₁ w₂ p₁ p₂, quot.sound (perm_product p₁ p₂))

infix * := product

theorem empty_product (s : finset B) : @empty A * s = ∅ :=
quot.induction_on s (λ l, rfl)

theorem mem_product {a : A} {b : B} {s₁ : finset A} {s₂ : finset B}
        : a ∈ s₁ → b ∈ s₂ → (a, b) ∈ s₁ * s₂ :=
quot.induction_on₂ s₁ s₂ (λ l₁ l₂ i₁ i₂, list.mem_product i₁ i₂)

theorem mem_of_mem_product_left {a : A} {b : B} {s₁ : finset A} {s₂ : finset B}
        : (a, b) ∈ s₁ * s₂ → a ∈ s₁ :=
quot.induction_on₂ s₁ s₂ (λ l₁ l₂ i, list.mem_of_mem_product_left i)

theorem mem_of_mem_product_right {a : A} {b : B} {s₁ : finset A} {s₂ : finset B}
        : (a, b) ∈ s₁ * s₂ → b ∈ s₂ :=
quot.induction_on₂ s₁ s₂ (λ l₁ l₂ i, list.mem_of_mem_product_right i)

theorem product_empty (s : finset A) : s * @empty B = ∅ :=
ext (λ p,
  match p with
  | (a, b) := iff.intro
     (λ i, absurd (mem_of_mem_product_right i) !not_mem_empty)
     (λ i, absurd i !not_mem_empty)
  end)
end product
end finset
