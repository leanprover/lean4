/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad

Cardinality calculations for finite sets.
-/
import .to_set .bigops data.set.function data.nat.power data.nat.bigops
open nat eq.ops

namespace finset

variables {A B : Type}
variables [deceqA : decidable_eq A] [deceqB : decidable_eq B]
include deceqA

theorem card_add_card (s₁ s₂ : finset A) : card s₁ + card s₂ = card (s₁ ∪ s₂) + card (s₁ ∩ s₂) :=
begin
  induction s₂ with s₂ a ans2 IH,
   show card s₁ + card (∅:finset A) = card (s₁ ∪ ∅) + card (s₁ ∩ ∅),
    by rewrite [union_empty, card_empty, inter_empty],
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
        end)
end

theorem card_union (s₁ s₂ : finset A) : card (s₁ ∪ s₂) = card s₁ + card s₂ - card (s₁ ∩ s₂) :=
calc
  card (s₁ ∪ s₂) = card (s₁ ∪ s₂) + card (s₁ ∩ s₂) - card (s₁ ∩ s₂) : add_sub_cancel
             ... = card s₁ + card s₂ - card (s₁ ∩ s₂)               : card_add_card

theorem card_union_of_disjoint {s₁ s₂ : finset A} (H : s₁ ∩ s₂ = ∅) :
  card (s₁ ∪ s₂) = card s₁ + card s₂ :=
by rewrite [card_union, H]

theorem card_le_card_of_subset {s₁ s₂ : finset A} (H : s₁ ⊆ s₂) : card s₁ ≤ card s₂ :=
have H1 : s₁ ∩ (s₂ \ s₁) = ∅,
  from inter_eq_empty (take x, assume H1 H2, not_mem_of_mem_diff H2 H1),
calc
  card s₂ = card (s₁ ∪ (s₂ \ s₁))    : union_diff_cancel H
      ... = card s₁ + card (s₂ \ s₁) : card_union_of_disjoint H1
      ... ≥ card s₁                  : le_add_right

section card_image
open set
include deceqB

theorem card_image_eq_of_inj_on {f : A → B} {s : finset A} (H1 : inj_on f (ts s)) : card (image f s) = card s :=
begin
  induction s with t a H IH,
    { rewrite [card_empty] },
    { have H2 : ts t ⊆ ts (insert a t), by rewrite [-subset_eq_to_set_subset]; apply subset_insert,
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
                                ... = card (insert a t)               : card_insert_of_not_mem H
    }
end
end card_image

theorem Sum_const_eq_card_mul (s : finset A) (n : nat) : (∑ x ∈ s, n) = card s * n :=
begin
  induction s with s' a H IH,
    rewrite [Sum_empty, card_empty, zero_mul],
    rewrite [Sum_insert_of_not_mem _ H, IH, card_insert_of_not_mem H, add.comm,
             mul.right_distrib, one_mul]
end

theorem Sum_one_eq_card (s : finset A) : (∑ x ∈ s, (1 : nat)) = card s :=
eq.trans !Sum_const_eq_card_mul !mul_one

section deceqB
include deceqB

theorem card_Union_of_disjoint (s : finset A) (f : A → finset B) :
  (∀{a₁ a₂}, a₁ ∈ s → a₂ ∈ s → a₁ ≠ a₂ → f a₁ ∩ f a₂ = ∅) →
    card (⋃ x ∈ s, f x) = ∑ x ∈ s, card (f x) :=
finset.induction_on s
  (assume H, by rewrite [Union_empty, Sum_empty, card_empty])
  (take s' a, assume H : a ∉ s',
    assume IH,
    assume H1 : ∀ {a₁ a₂ : A}, a₁ ∈ insert a s' → a₂ ∈ insert a s' → a₁ ≠ a₂ → f a₁ ∩ f a₂ = ∅,
    have H2  : ∀ a₁ a₂ : A, a₁ ∈ s' → a₂ ∈ s' → a₁ ≠ a₂ → f a₁ ∩ f a₂ = ∅, from
      take a₁ a₂, assume H3 H4 H5,
      H1 (!mem_insert_of_mem H3) (!mem_insert_of_mem H4) H5,
    assert H6 : card (⋃ (x : A) ∈ s', f x) = ∑ (x : A) ∈ s', card (f x), from IH H2,
    have H7 : ∀ x, x ∈ s' → f a ∩ f x = ∅, from
      take x, assume xs',
      have anex : a ≠ x, from assume aex, (eq.subst aex H) xs',
      H1 !mem_insert (!mem_insert_of_mem xs') anex,
    assert H8 : f a ∩ (⋃ (x : A) ∈ s', f x) = ∅, from
      calc
        f a ∩ (⋃ (x : A) ∈ s', f x) = (⋃ (x : A) ∈ s', f a ∩ f x)  : inter_Union
                                ... = (⋃ (x : A) ∈ s', ∅)          : Union_ext H7
                                ... = ∅                            : Union_empty',
    by rewrite [Union_insert_of_not_mem _ H, Sum_insert_of_not_mem _ H,
                card_union_of_disjoint H8, H6])
end deceqB

end finset
