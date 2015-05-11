/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad

Cardinality calculations for finite sets.
-/
import data.finset.to_set data.set.function
open nat eq.ops

namespace finset

variables {A B : Type}
variables [deceqA : decidable_eq A] [deceqB : decidable_eq B]
include deceqA

theorem card_add_card (s₁ s₂ : finset A) : card s₁ + card s₂ = card (s₁ ∪ s₂) + card (s₁ ∩ s₂) :=
finset.induction_on s₂
  (show card s₁ + card ∅ = card (s₁ ∪ ∅) + card (s₁ ∩ ∅),
    by rewrite [union_empty, card_empty, inter_empty])
  (take s₂ a,
    assume ans2: a ∉ s₂,
    assume IH : card s₁ + card s₂ = card (s₁ ∪ s₂) + card (s₁ ∩ s₂),
    show card s₁ + card (insert a s₂) = card (s₁ ∪ (insert a s₂)) + card (s₁ ∩ (insert a s₂)),
    from decidable.by_cases
      (assume as1 : a ∈ s₁,
        assert H : a ∉ s₁ ∩ s₂, from assume H', ans2 (mem_of_mem_inter_right H'),
        begin
          rewrite [card_insert_of_not_mem ans2, union.comm, -insert_union, union.comm],
          rewrite [insert_union, insert_eq_of_mem as1, insert_eq, inter.distrib_left, inter.comm],
          rewrite [singleton_inter_of_mem as1, -insert_eq, card_insert_of_not_mem H, -*add.assoc],
          rewrite IH
        end)
      (assume ans1 : a ∉ s₁,
        assert H : a ∉ s₁ ∪ s₂, from assume H',
          or.elim (mem_or_mem_of_mem_union H') (assume as1, ans1 as1) (assume as2, ans2 as2),
        begin
          rewrite [card_insert_of_not_mem ans2, union.comm, -insert_union, union.comm],
          rewrite [card_insert_of_not_mem H, insert_eq, inter.distrib_left, inter.comm],
          rewrite [singleton_inter_of_not_mem ans1, empty_union, add.right_comm],
          rewrite [-add.assoc, IH]
        end))

theorem card_union (s₁ s₂ : finset A) : card (s₁ ∪ s₂) = card s₁ + card s₂ - card (s₁ ∩ s₂) :=
calc
  card (s₁ ∪ s₂) = card (s₁ ∪ s₂) + card (s₁ ∩ s₂) - card (s₁ ∩ s₂) : add_sub_cancel
             ... = card s₁ + card s₂ - card (s₁ ∩ s₂)               : card_add_card

theorem card_union_of_disjoint {s₁ s₂ : finset A} (H : disjoint s₁ s₂) :
  card (s₁ ∪ s₂) = card s₁ + card s₂ :=
by rewrite [card_union, ↑disjoint at H, inter_empty_of_disjoint H]

theorem card_le_card_of_subset {s₁ s₂ : finset A} (H : s₁ ⊆ s₂) : card s₁ ≤ card s₂ :=
have H1 : disjoint s₁ (s₂ \ s₁),
  from disjoint.intro (take x, assume H1 H2, not_mem_of_mem_diff H2 H1),
calc
  card s₂ = card (s₁ ∪ (s₂ \ s₁))    : union_diff_cancel H
      ... = card s₁ + card (s₂ \ s₁) : card_union_of_disjoint H1
      ... ≥ card s₁                  : le_add_right

section card_image
open set
include deceqB

theorem card_image_eq_of_inj_on {f : A → B} {s : finset A} :
  inj_on f (ts s) → card (image f s) = card s :=
finset.induction_on s
  (assume H : inj_on f (ts empty), calc
    card (image f empty) = 0          : card_empty
                     ... = card empty : card_empty)
  (take t a,
    assume H : a ∉ t,
    assume IH : inj_on f (ts t) → card (image f t) = card t,
    assume H1 : inj_on f (ts (insert a t)),
    have H2 : ts t ⊆ ts (insert a t), by rewrite [-subset_eq_to_set_subset]; apply subset_insert,
    have H3 : card (image f t) = card t, from IH (inj_on_of_inj_on_of_subset H1 H2),
    have H4 : f a ∉ image f t,
      proof
        assume H5 : f a ∈ image f t,
        obtain x (H6l : x ∈ t) (H6r : f x = f a), from exists_of_mem_image H5,
        have H7 : x = a, from H1 (mem_insert_of_mem _ H6l) !mem_insert H6r,
        show false, from H (H7 ▸ H6l)
      qed,
    calc
      card (image f (insert a t)) = card (insert (f a) (image f t)) : image_insert
                              ... = card (image f t) + 1            : card_insert_of_not_mem H4
                              ... = card t + 1                      : H3
                              ... = card (insert a t)               : card_insert_of_not_mem H)
end card_image

end finset
