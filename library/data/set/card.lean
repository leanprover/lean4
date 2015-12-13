/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad

Cardinality of finite sets.
-/
import .finite data.finset.card
open nat classical

namespace set

variable {A : Type}

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

theorem card_insert_of_not_mem {a : A} {s : set A} [finite s] (H : a ∉ s) :
  card (insert a s) = card s + 1 :=
by rewrite [↑card, to_finset_insert, -mem_to_finset_eq at H, finset.card_insert_of_not_mem H]

theorem card_insert_le (a : A) (s : set A) [finite s] :
  card (insert a s) ≤ card s + 1 :=
if H : a ∈ s then by rewrite [card_insert_of_mem H]; apply le_succ
else by rewrite [card_insert_of_not_mem H]

theorem card_singleton (a : A) : card '{a} = 1 :=
by rewrite [card_insert_of_not_mem !not_mem_empty, card_empty]

/- Note: the induction tactic does not work well with the set induction principle with the
   extra predicate "finite". -/
theorem eq_empty_of_card_eq_zero {s : set A} [finite s] : card s = 0 → s = ∅ :=
induction_on_finite s
  (by intro H; exact rfl)
  (begin
    intro a s' fins' anins IH H,
    rewrite (card_insert_of_not_mem anins) at H,
    apply nat.no_confusion H
  end)

theorem card_upto (n : ℕ) : card {i | i < n} = n :=
by rewrite [↑card, to_finset_upto, finset.card_upto]

theorem card_add_card (s₁ s₂ : set A) [finite s₁] [finite s₂] :
  card s₁ + card s₂ = card (s₁ ∪ s₂) + card (s₁ ∩ s₂) :=
begin
  rewrite [-to_set_to_finset s₁, -to_set_to_finset s₂],
  rewrite [-finset.to_set_union, -finset.to_set_inter, *card_to_set],
  apply finset.card_add_card
end

theorem card_union (s₁ s₂ : set A) [finite s₁] [finite s₂] :
  card (s₁ ∪ s₂) = card s₁ + card s₂ - card (s₁ ∩ s₂) :=
calc
  card (s₁ ∪ s₂) = card (s₁ ∪ s₂) + card (s₁ ∩ s₂) - card (s₁ ∩ s₂) : nat.add_sub_cancel
             ... = card s₁ + card s₂ - card (s₁ ∩ s₂)               : card_add_card s₁ s₂

theorem card_union_of_disjoint {s₁ s₂ : set A} [finite s₁] [finite s₂] (H : s₁ ∩ s₂ = ∅) :
  card (s₁ ∪ s₂) = card s₁ + card s₂ :=
by rewrite [card_union, H, card_empty]

theorem card_eq_card_add_card_diff {s₁ s₂ : set A} [finite s₁] [finite s₂] (H : s₁ ⊆ s₂) :
  card s₂ = card s₁ + card (s₂ \ s₁) :=
have H1 : s₁ ∩ (s₂ \ s₁) = ∅,
  from eq_empty_of_forall_not_mem (take x, assume H, (and.right (and.right H)) (and.left H)),
have s₂ = s₁ ∪ (s₂ \ s₁), from eq.symm (union_diff_cancel H),
calc
  card s₂ = card (s₁ ∪ (s₂ \ s₁))    : {this}
      ... = card s₁ + card (s₂ \ s₁) : card_union_of_disjoint H1

theorem card_le_card_of_subset {s₁ s₂ : set A} [finite s₁] [finite s₂] (H : s₁ ⊆ s₂) :
  card s₁ ≤ card s₂ :=
calc
  card s₂ = card s₁ + card (s₂ \ s₁) : card_eq_card_add_card_diff H
      ... ≥ card s₁                  : le_add_right

variable {B : Type}

theorem card_image_eq_of_inj_on {f : A → B} {s : set A} [finite s] (injfs : inj_on f s) :
  card (image f s) = card s :=
begin
  rewrite [↑card, to_finset_image];
  apply finset.card_image_eq_of_inj_on,
  rewrite to_set_to_finset,
  apply injfs
end

theorem card_le_of_inj_on (a : set A) (b : set B) [finite b]
    (Pex : ∃ f : A → B, inj_on f a ∧ (image f a ⊆ b)) :
  card a ≤ card b :=
by_cases
  (assume fina : finite a,
    obtain f H, from Pex,
    finset.card_le_of_inj_on (to_finset a) (to_finset b)
      (exists.intro f
        begin
          rewrite [finset.subset_eq_to_set_subset, finset.to_set_image, *to_set_to_finset],
          exact H
        end))
  (assume nfina : ¬ finite a,
    by rewrite [card_of_not_finite nfina]; exact !zero_le)

theorem card_image_le (f : A → B) (s : set A) [finite s] : card (image f s) ≤ card s :=
by rewrite [↑card, to_finset_image]; apply finset.card_image_le

theorem inj_on_of_card_image_eq {f : A → B} {s : set A} [finite s]
  (H : card (image f s) = card s) : inj_on f s :=
begin
  rewrite -to_set_to_finset,
  apply finset.inj_on_of_card_image_eq,
  rewrite [-to_finset_to_set (finset.image _ _), finset.to_set_image, to_set_to_finset],
  exact H
end

theorem card_pos_of_mem {a : A} {s : set A} [finite s] (H : a ∈ s) : card s > 0 :=
have (#finset a ∈ to_finset s), by rewrite [finset.mem_eq_mem_to_set, to_set_to_finset]; apply H,
finset.card_pos_of_mem this

theorem eq_of_card_eq_of_subset {s₁ s₂ : set A} [finite s₁] [finite s₂]
    (Hcard : card s₁ = card s₂) (Hsub : s₁ ⊆ s₂) :
  s₁ = s₂ :=
begin
  rewrite [-to_set_to_finset s₁, -to_set_to_finset s₂, -finset.eq_eq_to_set_eq],
  apply finset.eq_of_card_eq_of_subset Hcard,
  rewrite [to_finset_subset_to_finset_eq],
  exact Hsub
end

theorem exists_two_of_card_gt_one {s : set A} (H : 1 < card s) : ∃ a b, a ∈ s ∧ b ∈ s ∧ a ≠ b :=
assert fins : finite s, from
  by_contradiction
    (assume nfins, by rewrite [card_of_not_finite nfins at H]; apply !not_succ_le_zero H),
by rewrite [-to_set_to_finset s]; apply finset.exists_two_of_card_gt_one H

end set
