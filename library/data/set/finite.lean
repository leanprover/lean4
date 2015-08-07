/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad

The notion of "finiteness" for sets. This approach is not computational: for example, just because
an element  s : set A  satsifies  finite s  doesn't mean that we can compute the cardinality. For
a computational representation, use the finset type.
-/
import data.set.function data.finset logic.choice
open nat

variable {A : Type}

namespace set

definition finite [class] (s : set A) : Prop := ∃ (s' : finset A), s = finset.to_set s'

theorem finite_finset [instance] (s : finset A) : finite (finset.to_set s) :=
exists.intro s rfl

/- to finset: casts every set to a finite set -/

noncomputable definition to_finset (s : set A) : finset A :=
if fins : finite s then some fins else finset.empty

theorem to_finset_of_not_finite {s : set A} (nfins : ¬ finite s) : to_finset s = (#finset ∅) :=
by rewrite [↑to_finset, dif_neg nfins]

theorem to_set_to_finset (s : set A) [fins : finite s] : finset.to_set (to_finset s) = s :=
by rewrite [↑to_finset, dif_pos fins]; exact eq.symm (some_spec fins)

theorem mem_to_finset_eq (a : A) (s : set A) [fins : finite s] :
  (#finset a ∈ to_finset s) = (a ∈ s) :=
by rewrite [-to_set_to_finset at {2}]

theorem to_set_to_finset_of_not_finite {s : set A} (nfins : ¬ finite s) :
  finset.to_set (to_finset s) = ∅ :=
by rewrite [to_finset_of_not_finite nfins]

theorem to_finset_to_set (s : finset A) : to_finset (finset.to_set s) = s :=
by rewrite [finset.eq_eq_to_set_eq, to_set_to_finset (finset.to_set s)]

theorem to_finset_eq_of_to_set_eq {s : set A} {t : finset A} (H : finset.to_set t = s) :
  to_finset s = t :=
finset.eq_of_to_set_eq_to_set (by subst [s]; rewrite to_finset_to_set)

/- finiteness -/

theorem finite_of_to_set_to_finset_eq {s : set A} (H : finset.to_set (to_finset s) = s) :
  finite s :=
by rewrite -H; apply finite_finset

theorem finite_empty [instance] : finite (∅ : set A) :=
by rewrite [-finset.to_set_empty]; apply finite_finset

theorem to_finset_empty : to_finset (∅ : set A) = (#finset ∅) :=
to_finset_eq_of_to_set_eq !finset.to_set_empty

theorem finite_insert [instance] (a : A) (s : set A) [fins : finite s] : finite (insert a s) :=
exists.intro (finset.insert a (to_finset s))
  (by rewrite [finset.to_set_insert, to_set_to_finset])

theorem to_finset_insert (a : A) (s : set A) [fins : finite s] :
  to_finset (insert a s) = finset.insert a (to_finset s) :=
by apply to_finset_eq_of_to_set_eq; rewrite [finset.to_set_insert, to_set_to_finset]

example : finite '{1, 2, 3} := _

theorem finite_union [instance] (s t : set A) [fins : finite s] [fint : finite t] :
  finite (s ∪ t) :=
exists.intro (#finset to_finset s ∪ to_finset t)
  (by rewrite [finset.to_set_union, *to_set_to_finset])

theorem to_finset_union (s t : set A) [fins : finite s] [fint : finite t] :
  to_finset (s ∪ t) = (#finset to_finset s ∪ to_finset t) :=
by apply to_finset_eq_of_to_set_eq; rewrite [finset.to_set_union, *to_set_to_finset]

theorem finite_inter [instance] (s t : set A) [fins : finite s] [fint : finite t] :
  finite (s ∩ t) :=
exists.intro (#finset to_finset s ∩ to_finset t)
  (by rewrite [finset.to_set_inter, *to_set_to_finset])

theorem to_finset_inter (s t : set A) [fins : finite s] [fint : finite t] :
  to_finset (s ∩ t) = (#finset to_finset s ∩ to_finset t) :=
by apply to_finset_eq_of_to_set_eq; rewrite [finset.to_set_inter, *to_set_to_finset]

theorem finite_filter [instance] (s : set A) (p : A → Prop) [h : decidable_pred p]
    [fins : finite s] :
  finite {x ∈ s | p x}  :=
exists.intro (finset.filter p (to_finset s))
  (by rewrite [finset.to_set_filter, *to_set_to_finset])

theorem to_finset_filter (s : set A) (p : A → Prop) [h : decidable_pred p] [fins : finite s] :
  to_finset {x ∈ s | p x} = (#finset {x ∈ to_finset s | p x}) :=
by apply to_finset_eq_of_to_set_eq; rewrite [finset.to_set_filter, to_set_to_finset]

theorem finite_image [instance] {B : Type} [h : decidable_eq B] (f : A → B) (s : set A)
    [fins : finite s] :
  finite (f '[s]) :=
exists.intro (finset.image f (to_finset s))
  (by rewrite [finset.to_set_image, *to_set_to_finset])

theorem to_finset_image {B : Type} [h : decidable_eq B] (f : A → B) (s : set A)
    [fins : finite s] :
  to_finset (f '[s]) = (#finset f '[to_finset s]) :=
by apply to_finset_eq_of_to_set_eq; rewrite [finset.to_set_image, to_set_to_finset]

theorem finite_diff [instance] (s t : set A) [fins : finite s] : finite (s \ t) :=
!finite_filter

theorem to_finset_diff (s t : set A) [fins : finite s] [fint : finite t] :
  to_finset (s \ t) = (#finset to_finset s \ to_finset t) :=
by apply to_finset_eq_of_to_set_eq; rewrite [finset.to_set_diff, *to_set_to_finset]

theorem finite_subset {s t : set A} [fint : finite t] (ssubt : s ⊆ t) : finite s :=
by rewrite (eq_filter_of_subset ssubt); apply finite_filter

theorem to_finset_subset_to_finset_eq (s t : set A) [fins : finite s] [fint : finite t] :
  (#finset to_finset s ⊆ to_finset t) = (s ⊆ t) :=
by rewrite [finset.subset_eq_to_set_subset, *to_set_to_finset]

theorem finite_of_finite_insert {s : set A} {a : A} (finias : finite (insert a s)) : finite s :=
finite_subset (subset_insert a s)

theorem finite_upto [instance] (n : ℕ) : finite {i | i < n} :=
by rewrite [-finset.to_set_upto n]; apply finite_finset

theorem to_finset_upto (n : ℕ) : to_finset {i | i < n} = finset.upto n :=
by apply (to_finset_eq_of_to_set_eq !finset.to_set_upto)

-- question: how can I avoid the parenthesis in the notation below?
-- this didn't work: notation `𝒫`:max s := powerset s, nor variants

theorem finite_powerset (s : set A) [fins : finite s] : finite (𝒫 s) :=
assert H : (𝒫 s) = finset.to_set '[finset.to_set (#finset 𝒫 (to_finset s))],
  from setext (take t, iff.intro
    (suppose t ∈ 𝒫 s,
      assert t ⊆ s, from this,
      assert finite t, from finite_subset this,
      have (#finset to_finset t ∈ 𝒫 (to_finset s)),
        by rewrite [finset.mem_powerset_iff_subset, to_finset_subset_to_finset_eq]; apply `t ⊆ s`,
      mem_image this (by rewrite to_set_to_finset))
    (assume H',
      obtain t' [(tmem : (#finset t' ∈ 𝒫 (to_finset s))) (teq : finset.to_set t' = t)],
        from H',
      show t ⊆ s,
        begin
          rewrite [-teq, finset.mem_powerset_iff_subset at tmem, -to_set_to_finset s],
          rewrite -finset.subset_eq_to_set_subset, assumption
        end)),
by rewrite H; apply finite_image

/- induction for finite sets -/

theorem induction_finite [recursor 6] {P : set A → Prop}
    (H1 : P ∅)
    (H2 : ∀ ⦃a : A⦄, ∀ {s : set A} [fins : finite s], a ∉ s → P s → P (insert a s)) :
  ∀ (s : set A) [fins : finite s], P s :=
begin
  intro s fins,
  rewrite [-to_set_to_finset s],
  generalize to_finset s,
  intro s',
  induction s' using finset.induction with a s' nains ih,
    {rewrite finset.to_set_empty, apply H1},
  rewrite [finset.to_set_insert],
  apply H2,
    {rewrite -finset.mem_eq_mem_to_set, assumption},
  exact ih
end

theorem induction_on_finite {P : set A → Prop} (s : set A) [fins : finite s]
    (H1 : P ∅)
    (H2 : ∀ ⦃a : A⦄, ∀ {s : set A} [fins : finite s], a ∉ s → P s → P (insert a s)) :
  P s :=
induction_finite H1 H2 s

/- cardinality -/

noncomputable definition card (s : set A) := finset.card (set.to_finset s)

theorem card_to_set (s : finset A) : card (finset.to_set s) = finset.card s :=
by rewrite [↑card, to_finset_to_set]

theorem card_of_not_finite {s : set A} (nfins : ¬ finite s) : card s = 0 :=
by rewrite [↑card, to_finset_of_not_finite nfins]

theorem card_empty : card (∅ : set A) = 0 :=
by rewrite [-finset.to_set_empty, card_to_set]

theorem card_insert_of_mem {a : A} {s : set A} (H : a ∈ s) : card (insert a s) = card s :=
if fins : finite s then
  (by rewrite [↑card, to_finset_insert, -mem_to_finset_eq at H, finset.card_insert_of_mem H])
else
  (assert ¬ finite (insert a s), from suppose _, absurd (!finite_of_finite_insert this) fins,
    by rewrite [card_of_not_finite fins, card_of_not_finite this])

theorem card_insert_of_not_mem {a : A} {s : set A} [fins : finite s] (H : a ∉ s) :
  card (insert a s) = card s + 1 :=
by rewrite [↑card, to_finset_insert, -mem_to_finset_eq at H, finset.card_insert_of_not_mem H]

theorem card_insert_le (a : A) (s : set A) [fins : finite s] :
  card (insert a s) ≤ card s + 1 :=
if H : a ∈ s then by rewrite [card_insert_of_mem H]; apply le_succ
else by rewrite [card_insert_of_not_mem H]

theorem card_singleton (a : A) : card '{a} = 1 :=
by rewrite [card_insert_of_not_mem !not_mem_empty, card_empty]

/- Note: the induction tactic does not work well with the set induction principle with the
   extra predicate "finite". -/
theorem eq_empty_of_card_eq_zero {s : set A} [fins : finite s] : card s = 0 → s = ∅ :=
induction_on_finite s 
  (by intro H; exact rfl)
  (begin
    intro a s' fins' anins IH H,
    rewrite (card_insert_of_not_mem anins) at H,
    apply nat.no_confusion H 
  end)

theorem card_upto (n : ℕ) : card {i | i < n} = n :=
by rewrite [↑card, to_finset_upto, finset.card_upto]

theorem card_add_card (s₁ s₂ : set A) [fins₁ : finite s₁] [fins₂ : finite s₂] :
  card s₁ + card s₂ = card (s₁ ∪ s₂) + card (s₁ ∩ s₂) :=
begin
  rewrite [-to_set_to_finset s₁, -to_set_to_finset s₂],
  rewrite [-finset.to_set_union, -finset.to_set_inter, *card_to_set],
  apply finset.card_add_card
end

theorem card_union (s₁ s₂ : set A) [fins₁ : finite s₁] [fins₂ : finite s₂] : 
  card (s₁ ∪ s₂) = card s₁ + card s₂ - card (s₁ ∩ s₂) :=
calc
  card (s₁ ∪ s₂) = card (s₁ ∪ s₂) + card (s₁ ∩ s₂) - card (s₁ ∩ s₂) : add_sub_cancel
             ... = card s₁ + card s₂ - card (s₁ ∩ s₂)               : card_add_card s₁ s₂

theorem card_union_of_disjoint {s₁ s₂ : set A} [fins₁ : finite s₁] [fins₂ : finite s₂] (H : s₁ ∩ s₂ = ∅) :
  card (s₁ ∪ s₂) = card s₁ + card s₂ :=
by rewrite [card_union, H, card_empty]

theorem card_eq_card_add_card_diff {s₁ s₂ : set A} [fins₁ : finite s₁] [fins₂ : finite s₂] (H : s₁ ⊆ s₂) :
  card s₂ = card s₁ + card (s₂ \ s₁) :=
have H1 : s₁ ∩ (s₂ \ s₁) = ∅,
  from eq_empty_of_forall_not_mem (take x, assume H, (and.right (and.right H)) (and.left H)),
have s₂ = s₁ ∪ (s₂ \ s₁), from eq.symm (union_diff_cancel H),
calc
  card s₂ = card (s₁ ∪ (s₂ \ s₁))    : {this}
      ... = card s₁ + card (s₂ \ s₁) : card_union_of_disjoint H1

theorem card_le_card_of_subset {s₁ s₂ : set A} [fins₁ : finite s₁] [fins₂ : finite s₂] (H : s₁ ⊆ s₂) : 
  card s₁ ≤ card s₂ :=
calc
  card s₂ = card s₁ + card (s₂ \ s₁) : card_eq_card_add_card_diff H
      ... ≥ card s₁                  : le_add_right

end set
