/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
import data.finset.card
open nat decidable

namespace finset
variable {A : Type}

protected definition to_nat (s : finset nat) : nat :=
finset.Sum s (λ n, 2^n)

open finset (to_nat)

lemma to_nat_empty : to_nat ∅ = 0 :=
rfl

lemma to_nat_insert {n : nat} {s : finset nat} : n ∉ s → to_nat (insert n s) = 2^n + to_nat s :=
assume h, Sum_insert_of_not_mem _ h

protected definition of_nat (s : nat) : finset nat :=
{ n ∈ upto (succ s) | odd (s / 2^n) }

open finset (of_nat)

private lemma of_nat_zero : of_nat 0 = ∅ :=
rfl

private lemma odd_of_mem_of_nat {n : nat} {s : nat} : n ∈ of_nat s → odd (s / 2^n) :=
assume h, of_mem_sep h

private lemma mem_of_nat_of_odd {n : nat} {s : nat} : odd (s / 2^n) → n ∈ of_nat s :=
assume h,
have 2^n < succ s, from by_contradiction
  (suppose ¬(2^n < succ s),
   assert 2^n > s, from lt_of_succ_le (le_of_not_gt this),
   assert s / 2^n = 0, from div_eq_zero_of_lt this,
   by rewrite this at h; exact absurd h dec_trivial),
have n < succ s,        from calc
   n   ≤ 2^n    : le_pow_self dec_trivial n
   ... < succ s : this,
have n ∈ upto (succ s), from mem_upto_of_lt this,
mem_sep_of_mem this h

private lemma succ_mem_of_nat (n : nat) (s : nat) : succ n ∈ of_nat s ↔ n ∈ of_nat (s / 2) :=
iff.intro
  (suppose succ n ∈ of_nat s,
   assert odd (s / 2^(succ n)),    from odd_of_mem_of_nat this,
   have odd ((s / 2) / (2 ^ n)), by rewrite [pow_succ' at this, nat.div_div_eq_div_mul, mul.comm]; assumption,
   show n ∈ of_nat (s / 2),        from mem_of_nat_of_odd this)
  (suppose n ∈ of_nat (s / 2),
   assert odd ((s / 2) / (2 ^ n)), from odd_of_mem_of_nat this,
   assert odd (s / 2^(succ n)),      by rewrite [pow_succ', mul.comm, -nat.div_div_eq_div_mul]; assumption,
   show succ n ∈ of_nat s,             from mem_of_nat_of_odd this)

private lemma odd_of_zero_mem (s : nat) : 0 ∈ of_nat s ↔ odd s :=
begin
  unfold of_nat, rewrite [mem_sep_eq, pow_zero, nat.div_one, mem_upto_eq],
  show 0 < succ s ∧ odd s ↔ odd s, from
  iff.intro
    (assume h, and.right h)
    (assume h, and.intro (zero_lt_succ s) h)
end

private lemma even_of_not_zero_mem (s : nat) : 0 ∉ of_nat s ↔ even s :=
have aux : 0 ∉ of_nat s ↔ ¬odd s, from not_iff_not_of_iff (odd_of_zero_mem s),
iff.intro
  (suppose 0 ∉ of_nat s, even_of_not_odd (iff.mp aux this))
  (suppose even s, iff.mpr aux (not_odd_of_even this))

private lemma even_to_nat (s : finset nat) : even (to_nat s) ↔ 0 ∉ s :=
finset.induction_on s dec_trivial
  (λ a s nains ih,
    begin
      rewrite [to_nat_insert nains], apply iff.intro,
        suppose even (2^a + to_nat s), by_cases
          (suppose e : even (2^a), by_cases
            (suppose even (to_nat s),
              assert 0 ∉ s, from iff.mp ih this,
              suppose 0 ∈ insert a s, or.elim (eq_or_mem_of_mem_insert this)
                (suppose 0 = a, begin rewrite [-this at e], exact absurd e not_even_one end)
                (by contradiction))
            (suppose odd  (to_nat s), absurd `even (2^a + to_nat s)` (odd_add_of_even_of_odd `even (2^a)` this)))
          (suppose o : odd (2^a), by_cases
            (suppose even (to_nat s), absurd `even (2^a + to_nat s)` (odd_add_of_odd_of_even `odd (2^a)` this))
            (suppose odd  (to_nat s), suppose 0 ∈ insert a s, or.elim (eq_or_mem_of_mem_insert this)
              (suppose 0 = a,
                have even (to_nat s), from iff.mpr ih (by rewrite -this at nains; exact nains),
                absurd this `odd (to_nat s)`)
              (suppose 0 ∈ s,
                assert a ≠ 0, from suppose a = 0, by subst a; contradiction,
                begin
                  cases a with a, exact absurd rfl `0 ≠ 0`,
                  have odd (2*2^a),  by rewrite [pow_succ' at o, mul.comm]; exact o,
                  have even (2*2^a), from !even_two_mul,
                  exact absurd `even (2*2^a)` `odd (2*2^a)`
                end))),
        suppose 0 ∉ insert a s,
          have a ≠ 0, from suppose a = 0, absurd (by rewrite this; apply mem_insert) `0 ∉ insert a s`,
          have 0 ∉ s, from suppose 0 ∈ s, absurd (mem_insert_of_mem _ this) `0 ∉ insert a s`,
          have even (to_nat s), from iff.mpr ih this,
          match a with
          | 0         := suppose a = 0, absurd this `a ≠ 0`
          | (succ a') := suppose a = succ a',
            have even (2^(succ a')), by rewrite [pow_succ', mul.comm]; apply even_two_mul,
            even_add_of_even_of_even this `even (to_nat s)`
          end rfl
    end)

private lemma of_nat_eq_insert_zero {s : nat} : 0 ∉ of_nat s → of_nat (2^0 + s) = insert 0 (of_nat s) :=
assume h : 0 ∉ of_nat s,
assert even s,                  from iff.mp (even_of_not_zero_mem s) h,
have   odd (s+1),               from odd_succ_of_even this,
assert zmem : 0 ∈ of_nat (s+1), from iff.mpr (odd_of_zero_mem (s+1)) this,
obtain w (hw : s = 2*w),        from exists_of_even `even s`,
begin
  rewrite [pow_zero, add.comm, hw],
  show of_nat (2*w+1) = insert 0 (of_nat (2*w)), from
  finset.ext (λ n,
    match n with
    | 0      := iff.intro (λ h, !mem_insert) (λ h, by rewrite [hw at zmem]; exact zmem)
    | succ m :=
       assert d₁  : 1 / 2 = (0:nat),  from dec_trivial,
       assert aux : _, from calc
         succ m ∈ of_nat (2 * w + 1) ↔ m ∈ of_nat ((2*w+1) / 2) : succ_mem_of_nat
                  ...                ↔ m ∈ of_nat w             : by rewrite [add.comm, add_mul_div_self_left _ _ (dec_trivial : 2 > 0), d₁, zero_add]
                  ...                ↔ m ∈ of_nat (2*w / 2)     : by rewrite [mul.comm, nat.mul_div_cancel _ (dec_trivial : 2 > 0)]
                  ...                ↔ succ m ∈ of_nat (2*w)    : succ_mem_of_nat,
       iff.intro
         (λ hl, finset.mem_insert_of_mem _ (iff.mp aux hl))
         (λ hr, or.elim (eq_or_mem_of_mem_insert hr)
           (by contradiction)
           (iff.mpr aux))
    end)
end

private lemma of_nat_eq_insert : ∀ {n s : nat}, n ∉ of_nat s → of_nat (2^n + s) = insert n (of_nat s)
| 0        s h := of_nat_eq_insert_zero h
| (succ n) s h :=
  have n ∉ of_nat (s / 2),
    from iff.mp (not_iff_not_of_iff !succ_mem_of_nat) h,
  assert ih : of_nat (2^n + s / 2) = insert n (of_nat (s / 2)), from of_nat_eq_insert this,
  finset.ext (λ x,
  have gen : ∀ m, m ∈ of_nat (2^(succ n) + s) ↔ m ∈ insert (succ n) (of_nat s)
  | zero     :=
    have even (2^(succ n)), by rewrite [pow_succ', mul.comm]; apply even_two_mul,
    have aux₁ : odd (2^(succ n) + s) ↔ odd s, from iff.intro
      (suppose odd (2^(succ n) + s), by_contradiction
        (suppose ¬ odd s,
         have even s,                from even_of_not_odd this,
         have even (2^(succ n) + s), from even_add_of_even_of_even `even (2^(succ n))` this,
         absurd `odd (2^(succ n) + s)` (not_odd_of_even this)))
      (suppose odd s, odd_add_of_even_of_odd `even (2^(succ n))` this),
    have aux₂ : odd s ↔ 0 ∈ insert (succ n) (of_nat s), from iff.intro
      (suppose odd s, finset.mem_insert_of_mem _ (iff.mpr !odd_of_zero_mem this))
      (suppose 0 ∈ insert (succ n) (of_nat s), or.elim (eq_or_mem_of_mem_insert this)
         (by contradiction)
         (suppose 0 ∈ of_nat s, iff.mp !odd_of_zero_mem this)),
    calc
      0 ∈ of_nat (2^(succ n) + s) ↔ odd (2^(succ n) + s)           : odd_of_zero_mem
                             ...  ↔ odd s                          : aux₁
                             ...  ↔ 0 ∈ insert (succ n) (of_nat s) : aux₂
  | (succ m) :=
    assert aux : m ∈ insert n (of_nat (s / 2)) ↔ succ m ∈ insert (succ n) (of_nat s), from iff.intro
      (assume hl, or.elim (eq_or_mem_of_mem_insert hl)
        (suppose m = n,                by subst m; apply mem_insert)
        (suppose m ∈ of_nat (s / 2), finset.mem_insert_of_mem _ (iff.mpr !succ_mem_of_nat this)))
      (assume hr, or.elim (eq_or_mem_of_mem_insert hr)
        (suppose succ m = succ n,
         assert m = n, by injection this; assumption,
         by subst m; apply mem_insert)
        (suppose succ m ∈ of_nat s, finset.mem_insert_of_mem _ (iff.mp !succ_mem_of_nat this))),
    calc
      succ m ∈ of_nat (2^(succ n) + s) ↔ succ m ∈ of_nat (2^n * 2 + s)       : by rewrite pow_succ'
                                 ...   ↔ m ∈ of_nat ((2^n * 2 + s) / 2)      : succ_mem_of_nat
                                 ...   ↔ m ∈ of_nat (2^n + s / 2)            : by rewrite [add.comm, add_mul_div_self (dec_trivial : 2 > 0), add.comm]
                                 ...   ↔ m ∈ insert n (of_nat (s / 2))       : by rewrite ih
                                 ...   ↔ succ m ∈ insert (succ n) (of_nat s) : aux,
  gen x)

lemma of_nat_to_nat (s : finset nat) : of_nat (to_nat s) = s :=
finset.induction_on s rfl
  (λ a s nains ih, by rewrite [to_nat_insert nains, -ih at nains, of_nat_eq_insert nains, ih])

private definition predimage (s : finset nat) : finset nat :=
{ n ∈ image pred s | succ n ∈ s }

private lemma mem_image_pred_of_succ_mem {n : nat} {s : finset nat} : succ n ∈ s → n ∈ image pred s :=
assume h,
  assert pred (succ n) ∈ image pred s, from mem_image_of_mem _ h,
  begin rewrite [pred_succ at this], assumption end

private lemma mem_predimage_of_succ_mem {n : nat} {s : finset nat} : succ n ∈ s → n ∈ predimage s :=
assume h, begin unfold predimage, rewrite [mem_sep_eq], exact and.intro (mem_image_pred_of_succ_mem h) h end

private lemma succ_mem_of_mem_predimage {n : nat} {s : finset nat} : n ∈ predimage s → succ n ∈ s :=
begin
  unfold predimage, rewrite [mem_sep_eq],
  suppose n ∈ image pred s ∧ succ n ∈ s, and.right this
end

private lemma predimage_insert_zero (s : finset nat) : predimage (insert 0 s) = predimage s :=
finset.ext (λ n,
  begin
    unfold predimage, rewrite [*mem_sep_eq, image_insert, pred_zero], apply iff.intro,
    suppose n ∈ insert 0 (image pred s) ∧ succ n ∈ insert 0 s,
      have succ n ∈ s, from or.elim (eq_or_mem_of_mem_insert (and.right this))
        (by contradiction)
        (λ h, h),
      and.intro (mem_image_pred_of_succ_mem this) this,
    suppose n ∈ image pred s ∧ succ n ∈ s,
      obtain h₁ h₂, from this,
      and.intro (mem_insert_of_mem 0 h₁) (mem_insert_of_mem 0 h₂)
  end)

private lemma predimage_insert_succ (n : nat) (s : finset nat) : predimage (insert (succ n) s) = insert n (predimage s) :=
finset.ext (λ m,
  begin
    unfold predimage, rewrite [*mem_sep_eq, *image_insert, pred_succ, *mem_insert_eq, *mem_sep_eq], apply iff.intro,
      suppose (m = n ∨ m ∈ image pred s) ∧ (succ m = succ n ∨ succ m ∈ s),
        obtain h₁ h₂, from this,
        or.elim h₁
          (suppose m = n, or.inl this)
          (suppose m ∈ image pred s, or.elim h₂
            (suppose succ m = succ n, by injection this; left; assumption)
            (suppose succ m ∈ s, by right; split; repeat assumption)),
      suppose m = n ∨ m ∈ image pred s ∧ succ m ∈ s, or.elim this
        (suppose m = n, and.intro (or.inl this) (or.inl (by subst m)))
        (suppose m ∈ image pred s ∧ succ m ∈ s,
          obtain h₁ h₂, from this,
          and.intro (or.inr h₁) (or.inr h₂))
  end)

private lemma of_nat_div2 (s : nat) : of_nat (s / 2) = predimage (of_nat s) :=
finset.ext (λ n, iff.intro
  (suppose n ∈ of_nat (s / 2),
   have succ n ∈ of_nat s, from iff.mpr !succ_mem_of_nat this,
   mem_predimage_of_succ_mem this)
  (suppose n ∈ predimage (of_nat s),
   have succ n ∈ of_nat s, from succ_mem_of_mem_predimage this,
   iff.mp !succ_mem_of_nat this))

private lemma to_nat_predimage (s : finset nat) : to_nat (predimage s) = (to_nat s) / 2 :=
begin
  induction s with a s nains ih,
   reflexivity,
   cases a with a,
   { rewrite [predimage_insert_zero, ih, to_nat_insert nains, pow_zero],
     have 0 ∉ of_nat (to_nat s), begin rewrite of_nat_to_nat, exact nains end,
     have even (to_nat s), from iff.mp !even_of_not_zero_mem this,
     obtain (w : nat) (hw : to_nat s = 2*w), from exists_of_even this,
     begin
       rewrite hw,
       have d₁ : 1 / 2 = (0:nat),          from dec_trivial,
       show 2 * w / 2 = (1 + 2 * w) / 2, by
         rewrite [add_mul_div_self_left _ _ (dec_trivial : 2 > 0), mul.comm,
                  nat.mul_div_cancel _ (dec_trivial : 2 > 0), d₁, zero_add]
     end },
   { have a ∉ predimage s, from suppose a ∈ predimage s, absurd (succ_mem_of_mem_predimage this) nains,
     rewrite [predimage_insert_succ, to_nat_insert nains, pow_succ', add.comm,
              add_mul_div_self (dec_trivial : 2 > 0), -ih, to_nat_insert this, add.comm] }
end

lemma to_nat_of_nat (s : nat) : to_nat (of_nat s) = s :=
nat.strong_induction_on s
  (λ n ih, by_cases
    (suppose n = 0, by rewrite this)
    (suppose n ≠ 0,
      have n / 2 < n, from div_lt_of_ne_zero this,
      have to_nat (of_nat (n / 2)) = n / 2, from ih _ this,
      have e₁ : to_nat (of_nat n) / 2 = n / 2, from calc
        to_nat (of_nat n) / 2 = to_nat (predimage (of_nat n)) : by rewrite to_nat_predimage
                          ...   = to_nat (of_nat (n / 2))     : by rewrite of_nat_div2
                          ...   = n / 2                       : this,
      have e₂ : even (to_nat (of_nat n)) ↔ even n, from calc
        even (to_nat (of_nat n)) ↔ 0 ∉ of_nat n : even_to_nat
                             ... ↔ even n       : even_of_not_zero_mem,
      eq_of_div2_of_even e₁ e₂))

open equiv

definition finset_nat_equiv_nat : finset nat ≃ nat :=
mk to_nat of_nat of_nat_to_nat to_nat_of_nat

end finset
