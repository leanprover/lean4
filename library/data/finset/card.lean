/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad

Cardinality calculations for finite sets.
-/
import data.finset.comb
open nat eq.ops

namespace finset

variable {A : Type}
variable [deceq : decidable_eq A]
include deceq

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

end finset
