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

infix [priority finset.prio] `'` := image

theorem image_empty (f : A → B) : image f ∅ = ∅ :=
rfl

theorem mem_image_of_mem (f : A → B) {s : finset A} {a : A} : a ∈ s → f a ∈ image f s :=
quot.induction_on s (take l, assume H : a ∈ elt_of l, mem_to_finset (mem_map f H))

theorem mem_image {f : A → B} {s : finset A} {a : A} {b : B}
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
    mem_image H₁ H₂)

theorem mem_image_eq (f : A → B) {s : finset A} {y : B} : y ∈ image f s = ∃x, x ∈ s ∧ f x = y :=
propext (mem_image_iff f)

theorem mem_image_of_mem_image_of_subset {f : A → B} {s t : finset A} {y : B}
    (H1 : y ∈ image f s) (H2 : s ⊆ t) : y ∈ image f t :=
obtain x (H3: x ∈ s) (H4 : f x = y), from exists_of_mem_image H1,
have H5 : x ∈ t, from mem_of_subset_of_mem H2 H3,
show y ∈ image f t, from mem_image H5 H4

theorem image_insert [h' : decidable_eq A] (f : A → B) (s : finset A) (a : A) :
  image f (insert a s) = insert (f a) (image f s) :=
ext (take y, iff.intro
  (assume H : y ∈ image f (insert a s),
    obtain x (H1l : x ∈ insert a s) (H1r :f x = y), from exists_of_mem_image H,
    have x = a ∨ x ∈ s, from eq_or_mem_of_mem_insert H1l,
    or.elim this
      (suppose x = a,
        have f a = y, from eq.subst this H1r,
        show y ∈ insert (f a) (image f s), from eq.subst this !mem_insert)
      (suppose x ∈ s,
        have f x ∈ image f s, from mem_image_of_mem f this,
        show y ∈ insert (f a) (image f s), from eq.subst H1r (mem_insert_of_mem _ this)))
  (suppose y ∈ insert (f a) (image f s),
    have y = f a ∨ y ∈ image f s, from eq_or_mem_of_mem_insert this,
    or.elim this
      (suppose y = f a,
        have f a ∈ image f (insert a s), from mem_image_of_mem f !mem_insert,
        show y ∈ image f (insert a s), from eq.subst (eq.symm `y = f a`) this)
      (suppose y ∈ image f s,
        show y ∈ image f (insert a s), from mem_image_of_mem_image_of_subset this !subset_insert)))

lemma image_compose {C : Type} [deceqC : decidable_eq C] {f : B → C} {g : A → B} {s : finset A} :
  image (f∘g) s = image f (image g s) :=
ext (take z, iff.intro
  (suppose z ∈ image (f∘g) s,
    obtain x (Hx : x ∈ s) (Hgfx : f (g x) = z), from exists_of_mem_image this,
    by rewrite -Hgfx; apply mem_image_of_mem _ (mem_image_of_mem _ Hx))
  (suppose z ∈ image f (image g s),
    obtain y (Hy : y ∈ image g s) (Hfy : f y = z), from exists_of_mem_image this,
    obtain x (Hx : x ∈ s) (Hgx : g x = y), from exists_of_mem_image Hy,
    mem_image Hx (by esimp; rewrite [Hgx, Hfy])))

lemma image_subset {a b : finset A} (f : A → B) (H : a ⊆ b) : f ' a ⊆ f ' b :=
subset_of_forall
  (take y, assume Hy : y ∈ f ' a,
    obtain x (Hx₁ : x ∈ a) (Hx₂ : f x = y), from exists_of_mem_image Hy,
    mem_image (mem_of_subset_of_mem H Hx₁) Hx₂)

theorem image_union [h' : decidable_eq A] (f : A → B) (s t : finset A) :
  image f (s ∪ t) = image f s ∪ image f t :=
ext (take y, iff.intro
  (assume H : y ∈ image f (s ∪ t),
    obtain x [(xst : x ∈ s ∪ t) (fxy : f x = y)], from exists_of_mem_image H,
    or.elim (mem_or_mem_of_mem_union xst)
      (assume xs, mem_union_l (mem_image xs fxy))
      (assume xt, mem_union_r (mem_image xt fxy)))
  (assume H : y ∈ image f s ∪ image f t,
    or.elim (mem_or_mem_of_mem_union H)
      (assume yifs : y ∈ image f s,
        obtain x [(xs : x ∈ s) (fxy : f x = y)], from exists_of_mem_image yifs,
        mem_image (mem_union_l xs) fxy)
      (assume yift : y ∈ image f t,
        obtain x [(xt : x ∈ t) (fxy : f x = y)], from exists_of_mem_image yift,
        mem_image (mem_union_r xt) fxy)))
end image

/- separation and set-builder notation -/
section sep
variables {A : Type} [deceq : decidable_eq A]
include deceq
variables (p : A → Prop) [decp : decidable_pred p] (s : finset A) {x : A}
include decp

definition sep : finset A :=
quot.lift_on s
  (λl, to_finset_of_nodup
    (list.filter p (subtype.elt_of l))
    (list.nodup_filter p (subtype.has_property l)))
  (λ l₁ l₂ u, quot.sound (perm.perm_filter u))

notation [priority finset.prio] `{` binder ` ∈ ` s ` | ` r:(scoped:1 p, sep p s) `}` := r

theorem sep_empty : sep p ∅ = ∅ := rfl

variables {p s}

theorem of_mem_sep : x ∈ sep p s → p x :=
quot.induction_on s (take l, list.of_mem_filter)

theorem mem_of_mem_sep : x ∈ sep p s → x ∈ s :=
quot.induction_on s (take l, list.mem_of_mem_filter)

theorem mem_sep_of_mem {x : A} : x ∈ s → p x → x ∈ sep p s :=
quot.induction_on s (take l, list.mem_filter_of_mem)

variables (p s)

theorem mem_sep_iff : x ∈ sep p s ↔ x ∈ s ∧ p x :=
iff.intro
  (assume H, and.intro (mem_of_mem_sep H) (of_mem_sep H))
  (assume H, mem_sep_of_mem (and.left H) (and.right H))

theorem mem_sep_eq : x ∈ sep p s = (x ∈ s ∧ p x) :=
propext !mem_sep_iff

variable t : finset A

theorem mem_sep_union_iff : x ∈ sep p (s ∪ t) ↔ x ∈ sep p s ∨ x ∈ sep p t :=
by rewrite [*mem_sep_iff, mem_union_iff, and.right_distrib]

end sep

section

variables {A : Type} [deceqA : decidable_eq A]
include deceqA

theorem eq_sep_of_subset {s t : finset A} (ssubt : s ⊆ t) : s = {x ∈ t | x ∈ s} :=
ext (take x, iff.intro
  (suppose x ∈ s, mem_sep_of_mem (mem_of_subset_of_mem ssubt this) this)
  (suppose x ∈ {x ∈ t | x ∈ s}, of_mem_sep this))

end

/- set difference -/
section diff
variables {A : Type} [deceq : decidable_eq A]
include deceq

definition diff (s t : finset A) : finset A := {x ∈ s | x ∉ t}
infix [priority finset.prio] ` \ `:70 := diff

theorem mem_of_mem_diff {s t : finset A} {x : A} (H : x ∈ s \ t) : x ∈ s :=
mem_of_mem_sep H

theorem not_mem_of_mem_diff {s t : finset A} {x : A} (H : x ∈ s \ t) : x ∉ t :=
of_mem_sep H

theorem mem_diff {s t : finset A} {x : A} (H1 : x ∈ s) (H2 : x ∉ t) : x ∈ s \ t :=
mem_sep_of_mem H1 H2

theorem mem_diff_iff (s t : finset A) (x : A) : x ∈ s \ t ↔ x ∈ s ∧ x ∉ t :=
iff.intro
  (assume H, and.intro (mem_of_mem_diff H) (not_mem_of_mem_diff H))
  (assume H, mem_diff (and.left H) (and.right H))

theorem mem_diff_eq (s t : finset A) (x : A) : x ∈ s \ t = (x ∈ s ∧ x ∉ t) :=
propext !mem_diff_iff

theorem union_diff_cancel {s t : finset A} (H : s ⊆ t) : s ∪ (t \ s) = t :=
ext (take x, iff.intro
  (suppose x ∈ s ∪ (t \ s),
    or.elim (mem_or_mem_of_mem_union this)
      (suppose x ∈ s, mem_of_subset_of_mem H this)
      (suppose x ∈ t \ s, mem_of_mem_diff this))
  (suppose x ∈ t,
    decidable.by_cases
      (suppose x ∈ s, mem_union_left _ this)
      (suppose x ∉ s, mem_union_right _ (mem_diff `x ∈ t` this))))

theorem diff_union_cancel {s t : finset A} (H : s ⊆ t) : (t \ s) ∪ s = t :=
eq.subst !union_comm (!union_diff_cancel H)
end diff

/- set complement -/
section complement

variables {A : Type} [deceqA : decidable_eq A] [h : fintype A]
include deceqA h

definition complement (s : finset A) : finset A := univ \ s
prefix [priority finset.prio] - := complement

theorem mem_complement {s : finset A} {x : A} (H : x ∉ s) : x ∈ -s :=
mem_diff !mem_univ H

theorem not_mem_of_mem_complement {s : finset A} {x : A} (H : x ∈ -s) : x ∉ s :=
not_mem_of_mem_diff H

theorem mem_complement_iff (s : finset A) (x : A) : x ∈ -s ↔ x ∉ s :=
iff.intro not_mem_of_mem_complement mem_complement

section
  open classical

  theorem union_eq_comp_comp_inter_comp (s t : finset A) : s ∪ t = -(-s ∩ -t) :=
  ext (take x, by rewrite [mem_union_iff, mem_complement_iff, mem_inter_iff, *mem_complement_iff,
                           or_iff_not_and_not])

  theorem inter_eq_comp_comp_union_comp (s t : finset A) : s ∩ t = -(-s ∪ -t) :=
  ext (take x, by rewrite [mem_inter_iff, mem_complement_iff, mem_union_iff, *mem_complement_iff,
                           and_iff_not_or_not])
end

end complement

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
  (suppose s ⊆ t, all_of_forall (take x, suppose x ∈ s, mem_of_subset_of_mem `s ⊆ t` `x ∈ s`))
  (suppose all s (λ x, x ∈ t), subset_of_forall (take x, suppose x ∈ s, of_mem_of_all `x ∈ s` `all s (λ x, x ∈ t)`))

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
  (λ v₁ v₂ w₁ w₂ p₁ p₂, begin apply @quot.sound, apply perm_product p₁ p₂ end)

infix [priority finset.prio] * := product

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

/- powerset -/
section powerset
variables {A : Type} [deceqA : decidable_eq A]
include deceqA

  section list_powerset
  open list

  definition list_powerset : list A → finset (finset A)
  | []       := '{∅}
  | (a :: l) := list_powerset l ∪ image (insert a) (list_powerset l)

  end list_powerset

private theorem image_insert_comm (a b : A) (s : finset (finset A)) :
  image (insert a) (image (insert b) s) = image (insert b) (image (insert a) s) :=
have aux' : ∀ a b : A, ∀ x : finset A,
  x ∈ image (insert a) (image (insert b) s) →
    x ∈ image (insert b) (image (insert a) s), from
  begin
    intros [a, b, x, H],
    cases (exists_of_mem_image H) with [y, Hy],
    cases Hy with [Hy1, Hy2],
    cases (exists_of_mem_image Hy1) with [z, Hz],
    cases Hz with [Hz1, Hz2],
    substvars,
    rewrite insert.comm,
    repeat (apply mem_image_of_mem),
    assumption
  end,
ext (take x, iff.intro (aux' a b x) (aux' b a x))

theorem list_powerset_eq_list_powerset_of_perm {l₁ l₂ : list A} (p : l₁ ~ l₂) :
    list_powerset l₁ = list_powerset l₂ :=
perm.induction_on p
  rfl
  (λ x l₁ l₂ p ih, by rewrite [↑list_powerset, ih])
  (λ x y l, by rewrite [↑list_powerset, ↑list_powerset, *image_union, image_insert_comm,
                        *union_assoc, union_left_comm (finset.image (finset.insert x) _)])
  (λ l₁ l₂ l₃ p₁ p₂ r₁ r₂, eq.trans r₁ r₂)

definition powerset (s : finset A) : finset (finset A) :=
quot.lift_on s
  (λ l, list_powerset (elt_of l))
  (λ l₁ l₂ p, list_powerset_eq_list_powerset_of_perm p)

prefix [priority finset.prio] `𝒫`:100 := powerset

theorem powerset_empty : 𝒫 (∅ : finset A) = '{∅} := rfl

theorem powerset_insert {a : A} {s : finset A} : a ∉ s → 𝒫 (insert a s) = 𝒫 s ∪ image (insert a) (𝒫 s) :=
quot.induction_on s
  (λ l,
    assume H : a ∉ quot.mk l,
    calc
      𝒫 (insert a (quot.mk l))
            = list_powerset (list.insert a (elt_of l)) : rfl
        ... = list_powerset (#list a :: elt_of l)       : by rewrite [list.insert_eq_of_not_mem H]
        ... = 𝒫 (quot.mk l) ∪ image (insert a) (𝒫 (quot.mk l)) : rfl)

theorem mem_powerset_iff_subset (s : finset A) : ∀ x, x ∈ 𝒫 s ↔ x ⊆ s :=
begin
  induction s with a s nains ih,
    intro x,
    rewrite powerset_empty,
    show x ∈ '{∅} ↔ x ⊆ ∅, by rewrite [mem_singleton_iff, subset_empty_iff],
  intro x,
    rewrite [powerset_insert nains, mem_union_iff, ih, mem_image_iff],
    exact
      (iff.intro
        (assume H,
          or.elim H
            (suppose x ⊆ s, subset.trans this !subset_insert)
            (suppose ∃ y, y ∈ 𝒫 s ∧ insert a y = x,
              obtain y [yps iay], from this,
              show x ⊆ insert a s,
                begin
                  rewrite [-iay],
                  apply insert_subset_insert,
                  rewrite -ih,
                  apply yps
                end))
        (assume H : x ⊆ insert a s,
          assert H' : erase a x ⊆ s, from erase_subset_of_subset_insert H,
          decidable.by_cases
            (suppose a ∈ x,
              or.inr (exists.intro (erase a x)
                (and.intro
                  (show erase a x ∈ 𝒫 s, by rewrite ih; apply H')
                  (show insert a (erase a x) = x, from insert_erase this))))
            (suppose a ∉ x, or.inl
              (show x ⊆ s, by rewrite [(erase_eq_of_not_mem this) at H']; apply H'))))
end

theorem subset_of_mem_powerset {s t : finset A} (H : s ∈ 𝒫 t) : s ⊆ t :=
iff.mp (mem_powerset_iff_subset t s) H

theorem mem_powerset_of_subset {s t : finset A} (H : s ⊆ t) : s ∈ 𝒫 t :=
iff.mpr (mem_powerset_iff_subset t s) H

theorem empty_mem_powerset (s : finset A) : ∅ ∈ 𝒫 s :=
mem_powerset_of_subset (empty_subset s)

end powerset
end finset
