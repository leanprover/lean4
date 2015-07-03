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
  induction s₂ with a s₂ ans2 IH,
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

theorem card_eq_card_add_card_diff {s₁ s₂ : finset A} (H : s₁ ⊆ s₂) :
  card s₂ = card s₁ + card (s₂ \ s₁) :=
have H1 : s₁ ∩ (s₂ \ s₁) = ∅,
  from inter_eq_empty (take x, assume H1 H2, not_mem_of_mem_diff H2 H1),
calc
  card s₂ = card (s₁ ∪ (s₂ \ s₁))    : union_diff_cancel H
      ... = card s₁ + card (s₂ \ s₁) : card_union_of_disjoint H1

theorem card_le_card_of_subset {s₁ s₂ : finset A} (H : s₁ ⊆ s₂) : card s₁ ≤ card s₂ :=
calc
  card s₂ = card s₁ + card (s₂ \ s₁) : card_eq_card_add_card_diff H
      ... ≥ card s₁                  : le_add_right

section card_image
open set
include deceqB

theorem card_image_eq_of_inj_on {f : A → B} {s : finset A} (H1 : inj_on f (ts s)) :
  card (image f s) = card s :=
begin
  induction s with a t H IH,
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

lemma card_le_of_inj_on (a : finset A) (b : finset B)
    (Pex : ∃ f : A → B, set.inj_on f (ts a) ∧ (image f a ⊆ b)):
  card a ≤ card b :=
obtain f Pinj, from Pex,
assert Psub : _, from and.right Pinj,
assert Ple : card (image f a) ≤ card b, from card_le_card_of_subset Psub,
by rewrite [(card_image_eq_of_inj_on (and.left Pinj))⁻¹]; exact Ple

theorem card_image_le (f : A → B) (s : finset A) : card (image f s) ≤ card s :=
finset.induction_on s
  (by rewrite finset.image_empty)
  (take a s',
    assume Ha : a ∉ s',
    assume IH : card (image f s') ≤ card s',
    begin
      rewrite [image_insert, card_insert_of_not_mem Ha],
      apply le.trans !card_insert_le,
      apply add_le_add_right IH
    end)

theorem inj_on_of_card_image_eq {f : A → B} {s : finset A} :
  card (image f s) = card s → inj_on f (ts s) :=
finset.induction_on s
  (by intro H; rewrite to_set_empty; apply inj_on_empty)
  (begin
    intro a s' Ha IH,
    rewrite [image_insert, card_insert_of_not_mem Ha, to_set_insert],
    assume H1 : card (insert (f a) (image f s')) = card s' + 1,
    show inj_on f (set.insert a (ts s')), from
      decidable.by_cases
        (assume Hfa : f a ∈ image f s',
           have H2 : card (image f s') = card s' + 1,
             by rewrite [card_insert_of_mem Hfa at H1]; assumption,
           absurd
             (calc
               card (image f s') ≤ card s'           : !card_image_le
                             ... < card s' + 1       : lt_succ_self
                             ... = card (image f s') : H2)
             !lt.irrefl)
        (assume Hnfa : f a ∉ image f s',
           have H2 : card (image f s') + 1 = card s' + 1,
             by rewrite [card_insert_of_not_mem Hnfa at H1]; assumption,
           have H3 : card (image f s') = card s', from add.cancel_right H2,
           have injf : inj_on f (ts s'), from IH H3,
           show inj_on f (set.insert a (ts s')), from
             take x1 x2,
             assume Hx1 : x1 ∈ set.insert a (ts s'),
             assume Hx2 : x2 ∈ set.insert a (ts s'),
             assume feq : f x1 = f x2,
             or.elim Hx1
               (assume Hx1' : x1 = a,
                 or.elim Hx2
                   (assume Hx2' : x2 = a, by rewrite [Hx1', Hx2'])
                   (assume Hx2' : x2 ∈ ts s',
                     have Hfa : f a ∈ image f s',
                       by rewrite [-Hx1', feq]; apply mem_image_of_mem f Hx2',
                     absurd Hfa Hnfa))
               (assume Hx1' : x1 ∈ ts s',
                 or.elim Hx2
                   (assume Hx2' : x2 = a,
                     have Hfa : f a ∈ image f s',
                       by rewrite [-Hx2', -feq]; apply mem_image_of_mem f Hx1',
                     absurd Hfa Hnfa)
                   (assume Hx2' : x2 ∈ ts s', injf Hx1' Hx2' feq)))
    end)

end card_image

theorem card_pos_of_mem {a : A} {s : finset A} (H : a ∈ s) : card s > 0 :=
begin
  induction s with a s' H1 IH,
  { contradiction },
  { rewrite (card_insert_of_not_mem H1), apply succ_pos }
end

theorem eq_of_card_eq_of_subset {s₁ s₂ : finset A} (Hcard : card s₁ = card s₂) (Hsub : s₁ ⊆ s₂) :
  s₁ = s₂ :=
have H : card s₁ + 0 = card s₁ + card (s₂ \ s₁),
  by rewrite [Hcard at {1}, card_eq_card_add_card_diff Hsub],
assert H1 : s₂ \ s₁ = ∅, from eq_empty_of_card_eq_zero (add.left_cancel H)⁻¹,
by rewrite [-union_diff_cancel Hsub, H1, union_empty]

theorem Sum_const_eq_card_mul (s : finset A) (n : nat) : (∑ x ∈ s, n) = card s * n :=
begin
  induction s with a s' H IH,
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
  (take a s', assume H : a ∉ s',
    assume IH,
    assume H1 : ∀ {a₁ a₂ : A}, a₁ ∈ insert a s' → a₂ ∈ insert a s' → a₁ ≠ a₂ → f a₁ ∩ f a₂ = ∅,
    have H2  : ∀ a₁ a₂ : A, a₁ ∈ s' → a₂ ∈ s' → a₁ ≠ a₂ → f a₁ ∩ f a₂ = ∅, from
      take a₁ a₂, assume H3 H4 H5,
      H1 (!mem_insert_of_mem H3) (!mem_insert_of_mem H4) H5,
    assert H6 : card (⋃ (x : A) ∈ s', f x) = ∑ (x : A) ∈ s', card (f x), from IH H2,
    assert H7 : ∀ x, x ∈ s' → f a ∩ f x = ∅, from
      take x, assume xs',
      have anex : a ≠ x, from assume aex, (eq.subst aex H) xs',
      H1 !mem_insert (!mem_insert_of_mem xs') anex,
    assert H8 : f a ∩ (⋃ (x : A) ∈ s', f x) = ∅, from
      calc
        f a ∩ (⋃ (x : A) ∈ s', f x) = (⋃ (x : A) ∈ s', f a ∩ f x)  : by rewrite inter_Union
                                ... = (⋃ (x : A) ∈ s', ∅)          : by rewrite [Union_ext H7]
                                ... = ∅                            : by rewrite Union_empty',
    by rewrite [Union_insert, Sum_insert_of_not_mem _ H,
                card_union_of_disjoint H8, H6])
end deceqB

lemma exists_two_of_card_gt_one {s : finset A} : 1 < card s → ∃ a b, a ∈ s ∧ b ∈ s ∧ a ≠ b :=
begin
  intro h,
  induction s with a s nain ih₁,
   {exact absurd h dec_trivial},
   {induction s with b s nbin ih₂,
    {exact absurd h dec_trivial},
     clear ih₁ ih₂,
     existsi a, existsi b, split,
      {apply mem_insert},
      split,
      {apply mem_insert_of_mem _ !mem_insert},
      {intro aeqb, subst a, exact absurd !mem_insert nain}}
end

lemma dvd_Sum_of_dvd (f : A → nat) (n : nat) (s : finset A) : (∀ a, a ∈ s → n ∣ f a) → n ∣ Sum s f :=
begin
  induction s with a s nain ih,
   {intros, rewrite [Sum_empty], apply dvd_zero},
   {intro h,
    have h₁ : ∀ a, a ∈ s → n ∣ f a, from
      take a, assume ains, h a (mem_insert_of_mem _ ains),
    have h₂ : n ∣ Sum s f, from ih h₁,
    have h₃ : n ∣ f a, from h a !mem_insert,
    rewrite [Sum_insert_of_not_mem f nain],
    apply dvd_add h₃ h₂}
end
end finset
