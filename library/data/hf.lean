/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura

Hereditarily finite sets: finite sets whose elements are all hereditarily finite sets.

Remark: all definitions compute, however the performace is quite poor since
we implement this module using a bijection from (finset nat) to nat, and
this bijection is implemeted using the Ackermann coding.
-/
import data.nat data.finset.equiv
open nat binary
open -[notations]finset

definition hf := nat

namespace hf
protected definition prio : num := num.succ std.priority.default

protected definition has_decidable_eq [instance] : decidable_eq hf :=
nat.has_decidable_eq

definition of_finset (s : finset hf) : hf :=
@equiv.to_fun _ _ finset_nat_equiv_nat s

definition to_finset (h : hf) : finset hf :=
@equiv.inv _ _ finset_nat_equiv_nat h

definition to_nat (h : hf) : nat :=
h

definition of_nat (n : nat) : hf :=
n

lemma to_finset_of_finset (s : finset hf) : to_finset (of_finset s) = s :=
@equiv.left_inv _ _ finset_nat_equiv_nat s

lemma of_finset_to_finset (s : hf) : of_finset (to_finset s) = s :=
@equiv.right_inv _ _ finset_nat_equiv_nat s

lemma to_finset_inj {s₁ s₂ : hf} : to_finset s₁ = to_finset s₂ → s₁ = s₂ :=
λ h, function.injective_of_left_inverse of_finset_to_finset h

lemma of_finset_inj {s₁ s₂ : finset hf} : of_finset s₁ = of_finset s₂ → s₁ = s₂ :=
λ h, function.injective_of_left_inverse to_finset_of_finset h

/- empty -/
definition empty : hf :=
of_finset (finset.empty)

notation `∅` := hf.empty

/- insert -/
definition insert (a s : hf) : hf :=
of_finset (finset.insert a (to_finset s))

/- mem -/
definition mem (a : hf) (s : hf) : Prop :=
finset.mem a (to_finset s)

infix `∈` := mem

definition not_mem (a : hf) (s : hf) : Prop := ¬ a ∈ s

infix `∉` := not_mem

open decidable
protected definition decidable_mem [instance] : ∀ a s, decidable (a ∈ s) :=
λ a s, finset.decidable_mem a (to_finset s)

lemma not_mem_empty (a : hf) : a ∉ ∅ :=
begin unfold [not_mem, mem, empty], rewrite to_finset_of_finset, apply finset.not_mem_empty end

lemma mem_insert (a s : hf) : a ∈ insert a s :=
begin unfold [mem, insert], rewrite to_finset_of_finset, apply finset.mem_insert end

lemma mem_insert_of_mem (a b s : hf) : a ∈ s → a ∈ insert b s :=
begin unfold [mem, insert], intros, rewrite to_finset_of_finset, apply finset.mem_insert_of_mem, assumption end

lemma eq_or_mem_of_mem_insert (a b s : hf) : a ∈ insert b s → a = b ∨ a ∈ s :=
begin unfold [mem, insert], rewrite to_finset_of_finset, intros, apply eq_or_mem_of_mem_insert, assumption  end

theorem mem_of_mem_insert_of_ne {x a : hf} {s : hf} : x ∈ insert a s → x ≠ a → x ∈ s :=
begin unfold [mem, insert], rewrite to_finset_of_finset, intros, apply mem_of_mem_insert_of_ne, repeat assumption end

protected theorem ext {s₁ s₂ : hf} : (∀ a, a ∈ s₁ ↔ a ∈ s₂) → s₁ = s₂ :=
assume h,
assert to_finset s₁ = to_finset s₂, from finset.ext h,
assert of_finset (to_finset s₁) = of_finset (to_finset s₂), by rewrite this,
by rewrite [*of_finset_to_finset at this]; exact this

theorem insert_eq_of_mem {a : hf} {s : hf} : a ∈ s → insert a s = s :=
begin unfold mem, intro h, unfold [mem, insert], rewrite (finset.insert_eq_of_mem h), rewrite of_finset_to_finset end

/- union -/
definition union (s₁ s₂ : hf) : hf :=
of_finset (finset.union (to_finset s₁) (to_finset s₂))

infix [priority hf.prio] ∪ := union

theorem mem_union_left {a : hf} {s₁ : hf} (s₂ : hf) : a ∈ s₁ → a ∈ s₁ ∪ s₂ :=
begin unfold mem, intro h, unfold union, rewrite to_finset_of_finset, apply finset.mem_union_left _ h end

theorem mem_union_l {a : hf} {s₁ : hf} {s₂ : hf} : a ∈ s₁ → a ∈ s₁ ∪ s₂ :=
mem_union_left s₂

theorem mem_union_right {a : hf} {s₂ : hf} (s₁ : hf) : a ∈ s₂ → a ∈ s₁ ∪ s₂ :=
begin unfold mem, intro h, unfold union, rewrite to_finset_of_finset, apply finset.mem_union_right _ h end

theorem mem_union_r {a : hf} {s₂ : hf} {s₁ : hf} : a ∈ s₂ → a ∈ s₁ ∪ s₂ :=
mem_union_right s₁

theorem mem_or_mem_of_mem_union {a : hf} {s₁ s₂ : hf} : a ∈ s₁ ∪ s₂ → a ∈ s₁ ∨ a ∈ s₂ :=
begin unfold [mem, union], rewrite to_finset_of_finset, intro h, apply finset.mem_or_mem_of_mem_union h end

theorem mem_union_iff {a : hf} (s₁ s₂ : hf) : a ∈ s₁ ∪ s₂ ↔ a ∈ s₁ ∨ a ∈ s₂ :=
iff.intro
 (λ h, mem_or_mem_of_mem_union h)
 (λ d, or.elim d
   (λ i, mem_union_left _ i)
   (λ i, mem_union_right _ i))

theorem mem_union_eq {a : hf} (s₁ s₂ : hf) : (a ∈ s₁ ∪ s₂) = (a ∈ s₁ ∨ a ∈ s₂) :=
propext !mem_union_iff

theorem union.comm (s₁ s₂ : hf) : s₁ ∪ s₂ = s₂ ∪ s₁ :=
hf.ext (λ a, by rewrite [*mem_union_eq]; exact or.comm)

theorem union.assoc (s₁ s₂ s₃ : hf) : (s₁ ∪ s₂) ∪ s₃ = s₁ ∪ (s₂ ∪ s₃) :=
hf.ext (λ a, by rewrite [*mem_union_eq]; exact or.assoc)

theorem union.left_comm (s₁ s₂ s₃ : hf) : s₁ ∪ (s₂ ∪ s₃) = s₂ ∪ (s₁ ∪ s₃) :=
!left_comm union.comm union.assoc s₁ s₂ s₃

theorem union.right_comm (s₁ s₂ s₃ : hf) : (s₁ ∪ s₂) ∪ s₃ = (s₁ ∪ s₃) ∪ s₂ :=
!right_comm union.comm union.assoc s₁ s₂ s₃

theorem union_self (s : hf) : s ∪ s = s :=
hf.ext (λ a, iff.intro
  (λ ain, or.elim (mem_or_mem_of_mem_union ain) (λ i, i) (λ i, i))
  (λ i, mem_union_left _ i))

theorem union_empty (s : hf) : s ∪ ∅ = s :=
hf.ext (λ a, iff.intro
  (suppose a ∈ s ∪ ∅, or.elim (mem_or_mem_of_mem_union this) (λ i, i) (λ i, absurd i !not_mem_empty))
  (suppose a ∈ s, mem_union_left _ this))

theorem empty_union (s : hf) : ∅ ∪ s = s :=
calc ∅ ∪ s = s ∪ ∅ : union.comm
       ... = s     : union_empty

/- inter -/
definition inter (s₁ s₂ : hf) : hf :=
of_finset (finset.inter (to_finset s₁) (to_finset s₂))

infix [priority hf.prio] ∩ := inter

theorem mem_of_mem_inter_left {a : hf} {s₁ s₂ : hf} : a ∈ s₁ ∩ s₂ → a ∈ s₁ :=
begin unfold mem, unfold inter, rewrite to_finset_of_finset, intro h, apply finset.mem_of_mem_inter_left h end

theorem mem_of_mem_inter_right {a : hf} {s₁ s₂ : hf} : a ∈ s₁ ∩ s₂ → a ∈ s₂ :=
begin unfold mem, unfold inter, rewrite to_finset_of_finset, intro h, apply finset.mem_of_mem_inter_right h end

theorem mem_inter {a : hf} {s₁ s₂ : hf} : a ∈ s₁ → a ∈ s₂ → a ∈ s₁ ∩ s₂ :=
begin unfold mem, intro h₁ h₂, unfold inter, rewrite to_finset_of_finset, apply finset.mem_inter h₁ h₂ end

theorem mem_inter_iff (a : hf) (s₁ s₂ : hf) : a ∈ s₁ ∩ s₂ ↔ a ∈ s₁ ∧ a ∈ s₂ :=
iff.intro
 (λ h, and.intro (mem_of_mem_inter_left h) (mem_of_mem_inter_right h))
 (λ h, mem_inter (and.elim_left h) (and.elim_right h))

theorem mem_inter_eq (a : hf) (s₁ s₂ : hf) : (a ∈ s₁ ∩ s₂) = (a ∈ s₁ ∧ a ∈ s₂) :=
propext !mem_inter_iff

theorem inter.comm (s₁ s₂ : hf) : s₁ ∩ s₂ = s₂ ∩ s₁ :=
hf.ext (λ a, by rewrite [*mem_inter_eq]; exact and.comm)

theorem inter.assoc (s₁ s₂ s₃ : hf) : (s₁ ∩ s₂) ∩ s₃ = s₁ ∩ (s₂ ∩ s₃) :=
hf.ext (λ a, by rewrite [*mem_inter_eq]; exact and.assoc)

theorem inter.left_comm (s₁ s₂ s₃ : hf) : s₁ ∩ (s₂ ∩ s₃) = s₂ ∩ (s₁ ∩ s₃) :=
!left_comm inter.comm inter.assoc s₁ s₂ s₃

theorem inter.right_comm (s₁ s₂ s₃ : hf) : (s₁ ∩ s₂) ∩ s₃ = (s₁ ∩ s₃) ∩ s₂ :=
!right_comm inter.comm inter.assoc s₁ s₂ s₃

theorem inter_self (s : hf) : s ∩ s = s :=
hf.ext (λ a, iff.intro
  (λ h, mem_of_mem_inter_right h)
  (λ h, mem_inter h h))

theorem inter_empty (s : hf) : s ∩ ∅ = ∅ :=
hf.ext (λ a, iff.intro
  (suppose a ∈ s ∩ ∅, absurd (mem_of_mem_inter_right this) !not_mem_empty)
  (suppose a ∈ ∅,     absurd this !not_mem_empty))

theorem empty_inter (s : hf) : ∅ ∩ s = ∅ :=
calc ∅ ∩ s = s ∩ ∅ : inter.comm
       ... = ∅     : inter_empty

/- card -/
definition card (s : hf) : nat :=
finset.card (to_finset s)

theorem card_empty : card ∅ = 0 :=
rfl

lemma ne_empty_of_card_eq_succ {s : hf} {n : nat} : card s = succ n → s ≠ ∅ :=
by intros; substvars; contradiction

/- erase -/
definition erase (a : hf) (s : hf) : hf :=
of_finset (erase a (to_finset s))

theorem mem_erase (a : hf) (s : hf) : a ∉ erase a s :=
begin unfold [not_mem, mem, erase], rewrite to_finset_of_finset, apply finset.mem_erase end

theorem card_erase_of_mem {a : hf} {s : hf} : a ∈ s → card (erase a s) = pred (card s) :=
begin unfold mem, intro h, unfold [erase, card], rewrite to_finset_of_finset, apply finset.card_erase_of_mem h end

theorem card_erase_of_not_mem {a : hf} {s : hf} : a ∉ s → card (erase a s) = card s :=
begin unfold [not_mem, mem], intro h, unfold [erase, card], rewrite to_finset_of_finset, apply finset.card_erase_of_not_mem h end

theorem erase_empty (a : hf) : erase a ∅ = ∅ :=
rfl

theorem ne_of_mem_erase {a b : hf} {s : hf} : b ∈ erase a s → b ≠ a :=
by intro h beqa; subst b; exact absurd h !mem_erase

theorem mem_of_mem_erase {a b : hf} {s : hf} : b ∈ erase a s → b ∈ s :=
begin unfold [erase, mem], rewrite to_finset_of_finset, intro h, apply mem_of_mem_erase h end

theorem mem_erase_of_ne_of_mem {a b : hf} {s : hf} : a ≠ b → a ∈ s → a ∈ erase b s :=
begin intro h₁, unfold mem, intro h₂, unfold erase, rewrite to_finset_of_finset, apply mem_erase_of_ne_of_mem h₁ h₂ end

theorem mem_erase_iff (a b : hf) (s : hf) : a ∈ erase b s ↔ a ∈ s ∧ a ≠ b :=
iff.intro
  (assume H, and.intro (mem_of_mem_erase H) (ne_of_mem_erase H))
  (assume H, mem_erase_of_ne_of_mem (and.right H) (and.left H))

theorem mem_erase_eq (a b : hf) (s : hf) : a ∈ erase b s = (a ∈ s ∧ a ≠ b) :=
propext !mem_erase_iff

theorem erase_insert {a : hf} {s : hf} : a ∉ s → erase a (insert a s) = s :=
begin
  unfold [not_mem, mem, erase, insert],
  intro h, rewrite [to_finset_of_finset, finset.erase_insert h, of_finset_to_finset]
end

theorem insert_erase {a : hf} {s : hf} : a ∈ s → insert a (erase a s) = s :=
begin
  unfold mem, intro h, unfold [insert, erase],
  rewrite [to_finset_of_finset, finset.insert_erase h, of_finset_to_finset]
end


/- subset -/
definition subset (s₁ s₂ : hf) : Prop :=
finset.subset (to_finset s₁) (to_finset s₂)

infix [priority hf.prio] `⊆` := subset

theorem empty_subset (s : hf) : ∅ ⊆ s :=
begin unfold [empty, subset], rewrite to_finset_of_finset, apply finset.empty_subset (to_finset s) end

theorem subset.refl (s : hf) : s ⊆ s :=
begin unfold [subset], apply finset.subset.refl (to_finset s) end

theorem subset.trans {s₁ s₂ s₃ : hf} : s₁ ⊆ s₂ → s₂ ⊆ s₃ → s₁ ⊆ s₃ :=
begin unfold [subset], intro h₁ h₂, apply finset.subset.trans h₁ h₂ end

theorem mem_of_subset_of_mem {s₁ s₂ : hf} {a : hf} : s₁ ⊆ s₂ → a ∈ s₁ → a ∈ s₂ :=
begin unfold [subset, mem], intro h₁ h₂, apply finset.mem_of_subset_of_mem h₁ h₂ end

theorem subset.antisymm {s₁ s₂ : hf} : s₁ ⊆ s₂ → s₂ ⊆ s₁ → s₁ = s₂ :=
begin unfold [subset], intro h₁ h₂, apply to_finset_inj (finset.subset.antisymm h₁ h₂) end

-- alternative name
theorem eq_of_subset_of_subset {s₁ s₂ : hf} (H₁ : s₁ ⊆ s₂) (H₂ : s₂ ⊆ s₁) : s₁ = s₂ :=
subset.antisymm H₁ H₂

theorem subset_of_forall {s₁ s₂ : hf} : (∀x, x ∈ s₁ → x ∈ s₂) → s₁ ⊆ s₂ :=
begin unfold [mem, subset], intro h, apply finset.subset_of_forall h end

theorem subset_insert (s : hf) (a : hf) : s ⊆ insert a s :=
begin unfold [subset, insert], rewrite to_finset_of_finset, apply finset.subset_insert (to_finset s) end

theorem eq_empty_of_subset_empty {x : hf} (H : x ⊆ ∅) : x = ∅ :=
subset.antisymm H (empty_subset x)

theorem subset_empty_iff (x : hf) : x ⊆ ∅ ↔ x = ∅ :=
iff.intro eq_empty_of_subset_empty (take xeq, by rewrite xeq; apply subset.refl ∅)

theorem erase_subset_erase (a : hf) {s t : hf} : s ⊆ t → erase a s ⊆ erase a t :=
begin unfold [subset, erase], intro h, rewrite *to_finset_of_finset, apply finset.erase_subset_erase a h end

theorem erase_subset  (a : hf) (s : hf) : erase a s ⊆ s :=
begin unfold [subset, erase], rewrite to_finset_of_finset, apply finset.erase_subset a (to_finset s) end

theorem erase_eq_of_not_mem {a : hf} {s : hf} : a ∉ s → erase a s = s :=
begin unfold [not_mem, mem, erase], intro h, rewrite [finset.erase_eq_of_not_mem h, of_finset_to_finset] end

theorem erase_insert_subset (a : hf) (s : hf) : erase a (insert a s) ⊆ s :=
begin unfold [erase, insert, subset], rewrite [*to_finset_of_finset], apply finset.erase_insert_subset a (to_finset s) end

theorem erase_subset_of_subset_insert {a : hf} {s t : hf} (H : s ⊆ insert a t) : erase a s ⊆ t :=
hf.subset.trans (!hf.erase_subset_erase H) (erase_insert_subset a t)

theorem insert_erase_subset (a : hf) (s : hf) : s ⊆ insert a (erase a s) :=
decidable.by_cases
  (assume ains : a ∈ s, by rewrite [!insert_erase ains]; apply subset.refl)
  (assume nains : a ∉ s, by rewrite[erase_eq_of_not_mem nains]; apply subset_insert)

theorem insert_subset_insert (a : hf) {s t : hf} : s ⊆ t → insert a s ⊆ insert a t :=
begin
  unfold [subset, insert], intro h,
  rewrite *to_finset_of_finset, apply finset.insert_subset_insert a h
end

theorem subset_insert_of_erase_subset {s t : hf} {a : hf} (H : erase a s ⊆ t) : s ⊆ insert a t :=
subset.trans (insert_erase_subset a s) (!insert_subset_insert H)

theorem subset_insert_iff (s t : hf) (a : hf) : s ⊆ insert a t ↔ erase a s ⊆ t :=
iff.intro !erase_subset_of_subset_insert !subset_insert_of_erase_subset

/- image -/
definition image (f : hf → hf) (s : hf) : hf :=
of_finset (finset.image f (to_finset s))

theorem image_empty (f : hf → hf) : image f ∅ = ∅ :=
rfl

theorem mem_image_of_mem (f : hf → hf) {s : hf} {a : hf} : a ∈ s → f a ∈ image f s :=
begin unfold [mem, image], intro h, rewrite to_finset_of_finset, apply finset.mem_image_of_mem f h end

theorem mem_image {f : hf → hf} {s : hf} {a : hf} {b : hf} (H1 : a ∈ s) (H2 : f a = b) : b ∈ image f s :=
eq.subst H2 (mem_image_of_mem f H1)

theorem exists_of_mem_image {f : hf → hf} {s : hf} {b : hf} : b ∈ image f s → ∃a, a ∈ s ∧ f a = b :=
begin unfold [mem, image], rewrite to_finset_of_finset, intro h, apply finset.exists_of_mem_image h end

theorem mem_image_iff (f : hf → hf) {s : hf} {y : hf} : y ∈ image f s ↔ ∃x, x ∈ s ∧ f x = y :=
begin unfold [mem, image], rewrite to_finset_of_finset, apply finset.mem_image_iff end

theorem mem_image_eq (f : hf → hf) {s : hf} {y : hf} : y ∈ image f s = ∃x, x ∈ s ∧ f x = y :=
propext (mem_image_iff f)

theorem mem_image_of_mem_image_of_subset {f : hf → hf} {s t : hf} {y : hf} (H1 : y ∈ image f s) (H2 : s ⊆ t) : y ∈ image f t :=
obtain x `x ∈ s` `f x = y`, from exists_of_mem_image H1,
have x ∈ t, from mem_of_subset_of_mem H2 `x ∈ s`,
show y ∈ image f t, from mem_image `x ∈ t` `f x = y`

theorem image_insert (f : hf → hf) (s : hf) (a : hf) : image f (insert a s) = insert (f a) (image f s) :=
begin unfold [image, insert], rewrite [*to_finset_of_finset, finset.image_insert] end

open function
lemma image_compose {f : hf → hf} {g : hf → hf} {s : hf} : image (f∘g) s = image f (image g s) :=
begin unfold image, rewrite [*to_finset_of_finset, finset.image_compose] end

lemma image_subset {a b : hf} (f : hf → hf) : a ⊆ b → image f a ⊆ image f b :=
begin unfold [subset, image], intro h, rewrite *to_finset_of_finset, apply finset.image_subset f h end

theorem image_union (f : hf → hf) (s t : hf) : image f (s ∪ t) = image f s ∪ image f t :=
begin unfold [image, union], rewrite [*to_finset_of_finset, finset.image_union] end

/- powerset -/
definition powerset (s : hf) : hf :=
of_finset (finset.image of_finset (finset.powerset (to_finset s)))

prefix [priority hf.prio] `𝒫`:100 := powerset

theorem powerset_empty : 𝒫 ∅ = insert ∅ ∅ :=
rfl

theorem powerset_insert {a : hf} {s : hf} : a ∉ s → 𝒫 (insert a s) = 𝒫 s ∪ image (insert a) (𝒫 s) :=
begin unfold [not_mem, mem, powerset, insert, union, image], rewrite [*to_finset_of_finset], intro h,
      have (λ (x : finset hf), of_finset (finset.insert a x)) = (λ (x : finset hf), of_finset (finset.insert a (to_finset (of_finset x)))), from
        funext (λ x, by rewrite to_finset_of_finset),
      rewrite [finset.powerset_insert h, finset.image_union, -*finset.image_compose,↑compose,this]
end

theorem mem_powerset_iff_subset (s : hf) : ∀ x : hf, x ∈ 𝒫 s ↔ x ⊆ s :=
begin
  intro x, unfold [mem, powerset, subset], rewrite [to_finset_of_finset, finset.mem_image_eq], apply iff.intro,
  suppose (∃ (w : finset hf), finset.mem w (finset.powerset (to_finset s)) ∧ of_finset w = x),
    obtain w h₁ h₂, from this,
    begin subst x, rewrite to_finset_of_finset, exact iff.mp !finset.mem_powerset_iff_subset h₁ end,
  suppose finset.subset (to_finset x) (to_finset s),
    assert finset.mem (to_finset x) (finset.powerset (to_finset s)), from iff.mpr !finset.mem_powerset_iff_subset this,
    exists.intro (to_finset x) (and.intro this (of_finset_to_finset x))
end

theorem subset_of_mem_powerset {s t : hf} (H : s ∈ 𝒫 t) : s ⊆ t :=
iff.mp (mem_powerset_iff_subset t s) H

theorem mem_powerset_of_subset {s t : hf} (H : s ⊆ t) : s ∈ 𝒫 t :=
iff.mpr (mem_powerset_iff_subset t s) H

theorem empty_mem_powerset (s : hf) : ∅ ∈ 𝒫 s :=
mem_powerset_of_subset (empty_subset s)
end hf
