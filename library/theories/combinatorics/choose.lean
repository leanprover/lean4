/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad

Binomial coefficients, "n choose k".
-/
import data.nat.div data.nat.fact data.finset
open decidable

namespace nat

/- choose -/

definition choose : ℕ → ℕ → ℕ
| 0 0               := 1
| 0 (succ k)        := 0
| (succ n) 0        := 1
| (succ n) (succ k) := choose n (succ k) + choose n k

theorem choose_zero_right (n : ℕ) : choose n 0 = 1 :=
nat.cases_on n rfl (take m, rfl)

theorem choose_zero_succ (k : ℕ) : choose 0 (succ k) = 0 := rfl

theorem choose_succ_succ (n k : ℕ) : choose (succ n) (succ k) = choose n (succ k) + choose n k :=
rfl

theorem choose_eq_zero_of_lt {n : ℕ} : ∀{k : ℕ}, n < k → choose n k = 0 :=
nat.induction_on n
  (take k, assume H : 0 < k,
    obtain k' (H : k = succ k'), from exists_eq_succ_of_pos H,
    by rewrite H)
  (take n',
    assume IH: ∀ k, n' < k → choose n' k = 0,
    take k,
    suppose succ n' < k,
    obtain k' (keq : k = succ k'), from exists_eq_succ_of_lt this,
    assert n' < k', by rewrite keq at this; apply lt_of_succ_lt_succ this,
    by rewrite [keq, choose_succ_succ, IH _ this, IH _ (lt.trans this !lt_succ_self)])

theorem choose_self (n : ℕ) : choose n n = 1 :=
begin
  induction n with [n, ih],
    {apply rfl},
  rewrite [choose_succ_succ, ih, choose_eq_zero_of_lt !lt_succ_self]
end

theorem choose_succ_self (n : ℕ) : choose (succ n) n = succ n :=
begin
  induction n with [n, ih],
    {apply rfl},
  rewrite [choose_succ_succ, ih, choose_self, add.comm]
end

theorem choose_one_right (n : ℕ) : choose n 1 = n :=
begin
  induction n with [n, ih],
    {apply rfl},
  rewrite [choose_succ_succ, ih, choose_zero_right]
end

theorem choose_pos {n : ℕ} : ∀ {k : ℕ}, k ≤ n → choose n k > 0 :=
begin
  induction n with [n, ih],
    {intros [k, H],
      have k = 0, from eq_of_le_of_ge H !zero_le,
      subst k, rewrite choose_zero_right; apply zero_lt_one},
  intro k,
  cases k with k,
    {intros, rewrite [choose_zero_right], apply zero_lt_one},
  suppose succ k ≤ succ n,
  assert k ≤ n, from le_of_succ_le_succ this,
  by rewrite [choose_succ_succ]; apply add_pos_right (ih this)
end

-- A key identity. The proof is subtle.
theorem succ_mul_choose_eq (n : ℕ) :
  ∀ k, succ n * (choose n k) = choose (succ n) (succ k) * succ k :=
begin
  induction n with [n, ih],
    {intro k,
      cases k with k',
        {rewrite [*choose_self, one_mul, mul_one]},
        {have H : 1 < succ (succ k'), from succ_lt_succ !zero_lt_succ,
          rewrite [one_mul, choose_zero_succ, choose_eq_zero_of_lt H, zero_mul]}},
  intro k,
  cases k with k',
    {rewrite [choose_zero_right, choose_one_right]},
  rewrite [choose_succ_succ (succ n), mul.right_distrib, -ih (succ k')],
  rewrite [choose_succ_succ at {1}, mul.left_distrib, *succ_mul (succ n), mul_succ, -ih k'],
  rewrite [*add.assoc, add.left_comm (choose n _)]
end

theorem choose_mul_fact_mul_fact {n : ℕ} :
  ∀ {k : ℕ}, k ≤ n → choose n k * fact k * fact (n - k) = fact n :=
begin
  induction n using nat.strong_induction_on with [n, ih],
  cases n with n,
    {intro k H, have k = 0, from eq_zero_of_le_zero H, rewrite this},
  intro k,
  intro H,  -- k ≤ n,
  cases k with k,
    {rewrite [choose_zero_right, fact_zero, *one_mul]},
  have k ≤ n, from le_of_succ_le_succ H,
  show choose (succ n) (succ k) * fact (succ k) * fact (succ n - succ k) = fact (succ n), from
  begin
    rewrite [succ_sub_succ, fact_succ, -mul.assoc, -succ_mul_choose_eq],
    rewrite [fact_succ n, -ih n !lt_succ_self this, *mul.assoc]
  end
end

theorem choose_def_alt {n k : ℕ} (H : k ≤ n) : choose n k = fact n div (fact k * fact (n -k)) :=
eq.symm (div_eq_of_eq_mul_left (mul_pos !fact_pos !fact_pos)
    (by rewrite [-mul.assoc, choose_mul_fact_mul_fact H]))

theorem fact_mul_fact_dvd_fact {n k : ℕ} (H : k ≤ n) : fact k * fact (n - k) ∣ fact n :=
by rewrite [-choose_mul_fact_mul_fact H, mul.assoc]; apply dvd_mul_left

open finset

/- the number of subsets of s of size k is n choose k -/

section card_subsets
variables {A : Type} [deceqA : decidable_eq A]
include deceqA

private theorem aux₀ (s : finset A) : {t ∈ powerset s | card t = 0} = '{∅} :=
ext (take t, iff.intro
  (assume H,
    assert t = ∅, from eq_empty_of_card_eq_zero (of_mem_filter H),
    show t ∈ '{ ∅ }, by rewrite [this, mem_singleton_eq'])
  (assume H,
    assert t = ∅, by rewrite mem_singleton_eq' at H; assumption,
    by substvars; exact mem_filter_of_mem !empty_mem_powerset rfl))

private theorem aux₁ (k : ℕ) : {t ∈ powerset (∅ : finset A) | card t = succ k} = ∅ :=
eq_empty_of_forall_not_mem (take t, assume H,
  assert t ∈ powerset ∅, from mem_of_mem_filter H,
  assert t = ∅, by rewrite [powerset_empty at this, mem_singleton_eq' at this]; assumption,
  have card (∅ : finset A) = succ k, by rewrite -this; apply of_mem_filter H,
  nat.no_confusion this)

private theorem aux₂ {a : A} {s t : finset A} (anins : a ∉ s) (tpows : t ∈ powerset s) : a ∉ t :=
suppose a ∈ t,
have a ∈ s, from mem_of_subset_of_mem (subset_of_mem_powerset tpows) this,
anins this

private theorem aux₃ {a : A} {s t : finset A} (anins : a ∉ s) (k : ℕ) :
  t ∈ (insert a) '[powerset s] ∧ card t = succ k ↔
    t ∈ (insert a) '[{t' ∈ powerset s | card t' = k}] :=
iff.intro
  (assume H,
    obtain H' cardt, from H,
    obtain t' [(t'pows : t' ∈ powerset s) (teq : insert a t' = t)], from exists_of_mem_image H',
    assert aint : a ∈ t, by rewrite -teq; apply mem_insert,
    assert anint' : a ∉ t', from
      (assume aint',
        have a ∈ s, from mem_of_subset_of_mem (subset_of_mem_powerset t'pows) aint',
        anins this),
    assert t' = erase a t, by rewrite [-teq, erase_insert (aux₂ anins t'pows)],
    have card t' = k, by rewrite [this, card_erase_of_mem aint, cardt],
    mem_image (mem_filter_of_mem t'pows this) teq)
  (assume H,
    obtain t' [Ht' (teq : insert a t' = t)], from exists_of_mem_image H,
    assert t'pows : t' ∈ powerset s, from mem_of_mem_filter Ht',
    assert cardt' : card t' = k, from of_mem_filter Ht',
    and.intro
      (show t ∈ (insert a) '[powerset s], from mem_image t'pows teq)
      (show card t = succ k,
        by rewrite [-teq, card_insert_of_not_mem (aux₂ anins t'pows), cardt']))

private theorem aux₄ {a : A} {s : finset A} (anins : a ∉ s) (k : ℕ) :
  {t ∈ powerset (insert a s)| card t = succ k} =
    {t ∈ powerset s | card t = succ k} ∪ (insert a) '[{t ∈ powerset s | card t = k}] :=
begin
  apply ext, intro t,
  rewrite [powerset_insert anins, mem_union_iff, *mem_filter_iff, mem_union_iff, and.right_distrib,
           aux₃ anins]
end

private theorem aux₅ {a : A} {s : finset A} (anins : a ∉ s) (k : ℕ) :
  {t ∈ powerset s | card t = succ k} ∩ (insert a) '[{t ∈ powerset s | card t = k}] = ∅ :=
inter_eq_empty
  (take t, assume Ht₁ Ht₂,
    have tpows : t ∈ powerset s, from mem_of_mem_filter Ht₁,
    have anint : a ∉ t, from aux₂ anins tpows,
    obtain t' [Ht' (teq : insert a t' = t)], from exists_of_mem_image Ht₂,
    have aint : a ∈ t, by rewrite -teq; apply mem_insert,
    show false, from anint aint)

private theorem aux₆ {a : A} {s : finset A} (anins : a ∉ s) (k : ℕ) :
  card ((insert a) '[{t ∈ powerset s | card t = k}]) = card {t ∈ powerset s | card t = k} :=
have set.inj_on (insert a) (ts {t ∈ powerset s| card t = k}), from
  take t₁ t₂, assume Ht₁ Ht₂,
  assume Heq : insert a t₁ = insert a t₂,
  have t₁ ∈ powerset s, from mem_of_mem_filter Ht₁,
  assert anint₁ : a ∉ t₁, from aux₂ anins this,
  have t₂ ∈ powerset s, from mem_of_mem_filter Ht₂,
  assert anint₂ : a ∉ t₂, from aux₂ anins this,
  calc
    t₁    = erase a (insert a t₁) : by rewrite (erase_insert anint₁)
      ... = erase a (insert a t₂) : Heq
      ... = t₂                    : by rewrite (erase_insert anint₂),
card_image_eq_of_inj_on this

theorem card_subsets (s : finset A) : ∀k, card {t ∈ powerset s | card t = k} = choose (card s) k :=
begin
  induction s with a s anins ih,
    {intro k,
      cases k with k,
        {rewrite aux₀},
      rewrite aux₁},
  intro k,
  cases k with k,
    {rewrite [aux₀, choose_zero_right]},
  rewrite [*(card_insert_of_not_mem anins), aux₄ anins, card_union_of_disjoint (aux₅ anins k),
           aux₆ anins k, *ih]
end

end card_subsets

end nat
