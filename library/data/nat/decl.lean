--- Copyright (c) 2014 Floris van Doorn. All rights reserved.
--- Released under Apache 2.0 license as described in the file LICENSE.
--- Author: Floris van Doorn, Leonardo de Moura
import logic.eq logic.heq logic.wf logic.decidable logic.if data.prod

open eq.ops decidable

inductive nat :=
zero : nat,
succ : nat → nat

namespace nat
  notation `ℕ` := nat

  inductive lt (a : nat) : nat → Prop :=
  base : lt a (succ a),
  step : Π {b}, lt a b → lt a (succ b)

  notation a < b := lt a b

  inductive le (a : nat) : nat → Prop :=
  refl    : le a a,
  of_lt : ∀ {b}, lt a b → le a b

  notation a ≤ b := le a b

  definition pred (a : nat) : nat :=
  cases_on a zero (λ a₁, a₁)

  protected definition is_inhabited [instance] : inhabited nat :=
  inhabited.mk zero

  protected definition has_decidable_eq [instance] : decidable_eq nat :=
  λn m : nat,
  have general : ∀n, decidable (n = m), from
    rec_on m
      (λ n, cases_on n
        (inl rfl)
        (λ m, inr (λ (e : succ m = zero), no_confusion e)))
      (λ (m' : nat) (ih : ∀n, decidable (n = m')) (n : nat), cases_on n
        (inr (λ h, no_confusion h))
        (λ (n' : nat),
          decidable.rec_on (ih n')
            (assume Heq : n' = m', inl (eq.rec_on Heq rfl))
            (assume Hne : n' ≠ m',
              have H1 : succ n' ≠ succ m', from
                assume Heq, no_confusion Heq (λ e : n' = m', Hne e),
              inr H1))),
  general n

  -- less-than is well-founded
  definition lt.wf [instance] : well_founded lt :=
  well_founded.intro (λn, rec_on n
    (acc.intro zero (λ (y : nat) (hlt : y < zero),
      have aux : ∀ {n₁}, y < n₁ → zero = n₁ → acc lt y, from
        λ n₁ hlt, lt.cases_on hlt
          (λ heq, no_confusion heq)
          (λ b hlt heq, no_confusion heq),
      aux hlt rfl))
    (λ (n : nat) (ih : acc lt n),
      acc.intro (succ n) (λ (m : nat) (hlt : m < succ n),
        have aux : ∀ {n₁} (hlt : m < n₁), succ n = n₁ → acc lt m, from
          λ n₁ hlt, lt.cases_on hlt
            (λ (heq : succ n = succ m),
              nat.no_confusion heq (λ (e : n = m),
                eq.rec_on e ih))
            (λ b (hlt : m < b) (heq : succ n = succ b),
              nat.no_confusion heq (λ (e : n = b),
                acc.inv (eq.rec_on e ih) hlt)),
        aux hlt rfl)))

  definition not_lt_zero (a : nat) : ¬ a < zero :=
  have aux : ∀ {b}, a < b → b = zero → false, from
    λ b H, lt.cases_on H
      (λ heq, nat.no_confusion heq)
      (λ b h₁ heq, nat.no_confusion heq),
  λ H, aux H rfl

  definition zero_lt_succ (a : nat) : zero < succ a :=
  rec_on a
    (lt.base zero)
    (λ a (hlt : zero < succ a), lt.step hlt)

  definition lt.trans {a b c : nat} (H₁ : a < b) (H₂ : b < c) : a < c :=
  have aux : ∀ {d}, d < c → b = d → a < b → a < c, from
    (λ d H, lt.rec_on H
      (λ h₁ h₂, lt.step (eq.rec_on h₁ h₂))
      (λ b hl ih h₁ h₂, lt.step (ih h₁ h₂))),
  aux H₂ rfl H₁

  definition lt.imp_succ {a b : nat} (H : a < b) : succ a < succ b :=
  lt.rec_on H
    (lt.base (succ a))
    (λ b hlt ih, lt.trans ih (lt.base (succ b)))

  definition lt.cancel_succ_left {a b : nat} (H : succ a < b) : a < b :=
  have aux : ∀ {a₁}, a₁ < b → succ a = a₁ → a < b, from
    λ a₁ H, lt.rec_on H
      (λ e₁, eq.rec_on e₁ (lt.step (lt.base a)))
      (λ d hlt ih e₁, lt.step (ih e₁)),
  aux H rfl

  definition lt.cancel_succ_left_right {a b : nat} (H : succ a < succ b) : a < b :=
  have aux : pred (succ a) < pred (succ b), from
    lt.rec_on H
      (lt.base a)
      (λ (b : nat) (hlt : succ a < b) ih,
        show pred (succ a) < pred (succ b), from
        lt.cancel_succ_left hlt),
  aux

  definition lt.is_decidable_rel [instance] : decidable_rel lt :=
  λ a b, rec_on b
    (λ (a : nat), inr (not_lt_zero a))
    (λ (b₁ : nat) (ih : ∀ a, decidable (a < b₁)) (a : nat), cases_on a
       (inl !zero_lt_succ)
       (λ a, decidable.rec_on (ih a)
         (λ h_pos : a < b₁, inl (lt.imp_succ h_pos))
         (λ h_neg : ¬ a < b₁,
           have aux : ¬ succ a < succ b₁, from
             λ h : succ a < succ b₁, h_neg (lt.cancel_succ_left_right h),
           inr aux)))
    a

  definition le_def_right {a b : nat} (H : a ≤ b) : a = b ∨ a < b :=
  le.cases_on H
    (or.inl rfl)
    (λ b hlt, or.inr hlt)

  definition le_def_left {a b : nat} (H : a = b ∨ a < b) : a ≤ b :=
  or.rec_on H
    (λ hl, eq.rec_on hl !le.refl)
    (λ hr, le.of_lt hr)

  definition le.is_decidable_rel [instance] : decidable_rel le :=
  λ a b, decidable_iff_equiv _ (iff.intro le_def_left le_def_right)

  definition lt.irrefl (a : nat) : ¬ a < a :=
  rec_on a
    !not_lt_zero
    (λ (a : nat) (ih : ¬ a < a) (h : succ a < succ a),
      ih (lt.cancel_succ_left_right h))

  definition lt.asymm {a b : nat} (H : a < b) : ¬ b < a :=
  lt.rec_on H
    (λ h : succ a < a, !lt.irrefl (lt.cancel_succ_left h))
    (λ b hlt (ih : ¬ b < a) (h : succ b < a), ih (lt.cancel_succ_left h))

  definition lt.trichotomy (a b : nat) : a < b ∨ a = b ∨ b < a :=
  rec_on b
    (λa, cases_on a
       (or.inr (or.inl rfl))
       (λ a₁, or.inr (or.inr !zero_lt_succ)))
    (λ b₁ (ih : ∀a, a < b₁ ∨ a = b₁ ∨ b₁ < a) (a : nat), cases_on a
       (or.inl !zero_lt_succ)
       (λ a, or.rec_on (ih a)
           (λ h : a < b₁, or.inl (lt.imp_succ h))
           (λ h, or.rec_on h
              (λ h : a = b₁, or.inr (or.inl (eq.rec_on h rfl)))
              (λ h : b₁ < a, or.inr (or.inr (lt.imp_succ h))))))
    a

  definition not_lt {a b : nat} (hnlt : ¬ a < b) : a = b ∨ b < a :=
  or.rec_on (lt.trichotomy a b)
    (λ hlt, absurd hlt hnlt)
    (λ h, h)

  definition le_imp_lt_succ {a b : nat} (h : a ≤ b) : a < succ b :=
  le.rec_on h
    (lt.base a)
    (λ b h, lt.step h)

  definition le_succ_imp_lt {a b : nat} (h : succ a ≤ b) : a < b :=
  le.rec_on h
    (lt.base a)
    (λ b (h : succ a < b), lt.cancel_succ_left_right (lt.step h))

  definition le.step {a b : nat} (h : a ≤ b) : a ≤ succ b :=
  le.rec_on h
    (le.of_lt (lt.base a))
    (λ b (h : a < b), le.of_lt (lt.step h))

  definition lt_imp_le_succ {a b : nat} (h : a < b) : succ a ≤ b :=
  lt.rec_on h
    (le.refl (succ a))
    (λ b hlt (ih : succ a ≤ b), le.step ih)

  definition le.trans {a b c : nat} (h₁ : a ≤ b) : b ≤ c → a ≤ c :=
  le.rec_on h₁
    (λ h, h)
    (λ b (h₁ : a < b) (h₂ : b ≤ c), le.rec_on h₂
      (le.of_lt h₁)
      (λ c (h₂ : b < c), le.of_lt (lt.trans h₁ h₂)))

  definition le_lt.trans {a b c : nat} (h₁ : a ≤ b) : b < c → a < c :=
  le.rec_on h₁
    (λ h, h)
    (λ b (h₁ : a < b) (h₂ : b < c), lt.trans h₁ h₂)

  definition lt_le.trans {a b c : nat} (h₁ : a < b) (h₂ : b ≤ c) : a < c :=
  le.rec_on h₂
    h₁
    (λ c (h₂ : b < c), lt.trans h₁ h₂)

  definition lt_eq.trans {a b c : nat} (h₁ : a < b) (h₂ : b = c) : a < c :=
  eq.rec_on h₂ h₁

  definition le_eq.trans {a b c : nat} (h₁ : a ≤ b) (h₂ : b = c) : a ≤ c :=
  eq.rec_on h₂ h₁

  definition eq_lt.trans {a b c : nat} (h₁ : a = b) (h₂ : b < c) : a < c :=
  eq.rec_on (eq.rec_on h₁ rfl) h₂

  definition eq_le.trans {a b c : nat} (h₁ : a = b) (h₂ : b ≤ c) : a ≤ c :=
  eq.rec_on (eq.rec_on h₁ rfl) h₂

  calc_trans lt.trans
  calc_trans le.trans
  calc_trans le_lt.trans
  calc_trans lt_le.trans
  calc_trans lt_eq.trans
  calc_trans le_eq.trans
  calc_trans eq_lt.trans
  calc_trans eq_le.trans

  definition max (a b : nat) : nat :=
  if a < b then b else a

  definition min (a b : nat) : nat :=
  if a < b then a else b

  definition max_a_a (a : nat) : a = max a a :=
  eq.rec_on !if_t_t rfl

  definition max.eq_right {a b : nat} (H : a < b) : max a b = b :=
  if_pos H

  definition max.eq_left {a b : nat} (H : ¬ a < b) : max a b = a :=
  if_neg H

  definition max.eq_right_symm {a b : nat} (H : a < b) : b = max a b :=
  eq.rec_on (max.eq_right H) rfl

  definition max.eq_left_symm {a b : nat} (H : ¬ a < b) : a = max a b :=
  eq.rec_on (max.eq_left H) rfl

  definition max.left (a b : nat) : a ≤ max a b :=
  by_cases
    (λ h : a < b,   le.of_lt (eq.rec_on (max.eq_right_symm h) h))
    (λ h : ¬ a < b, eq.rec_on (max.eq_left h) !le.refl)

  definition max.right (a b : nat) : b ≤ max a b :=
  by_cases
    (λ h : a < b,   eq.rec_on (max.eq_right h) !le.refl)
    (λ h : ¬ a < b, or.rec_on (not_lt h)
      (λ heq, eq.rec_on heq (eq.rec_on (max_a_a a) !le.refl))
      (λ h : b < a,
        have aux : a = max a b, from max.eq_left_symm (lt.asymm h),
        eq.rec_on aux (le.of_lt h)))

  definition gt a b := lt b a

  notation a > b := gt a b

  definition ge a b := le b a

  notation a ≥ b := ge a b

  definition add (a b : nat) : nat :=
  rec_on b a (λ b₁ r, succ r)

  notation a + b := add a b

  definition sub (a b : nat) : nat :=
  rec_on b a (λ b₁ r, pred r)

  notation a - b := sub a b

  definition mul (a b : nat) : nat :=
  rec_on b zero (λ b₁ r, r + a)

  notation a * b := mul a b

  definition sub.succ_succ (a b : nat) : succ a - succ b = a - b :=
  induction_on b
    rfl
    (λ b₁ (ih : succ a - succ b₁ = a - b₁),
      eq.rec_on ih (eq.refl (pred (succ a - succ b₁))))

  definition sub.succ_succ_symm (a b : nat) : a - b = succ a - succ b :=
  eq.rec_on (sub.succ_succ a b) rfl

  definition sub.zero_left (a : nat) : zero - a = zero :=
  induction_on a
    rfl
    (λ a₁ (ih : zero - a₁ = zero),
      eq.rec_on ih (eq.refl (pred (zero - a₁))))

  definition sub.zero_left_symm (a : nat) : zero = zero - a :=
  eq.rec_on (sub.zero_left a) rfl

  definition sub.lt {a b : nat} : zero < a → zero < b → a - b < a :=
  have aux : Π {a}, zero < a → Π {b}, zero < b → a - b < a, from
    λa h₁, lt.rec_on h₁
      (λb h₂, lt.cases_on h₂
        (lt.base zero)
        (λ b₁ bpos,
          eq.rec_on (sub.succ_succ_symm zero b₁)
           (eq.rec_on (sub.zero_left_symm b₁) (lt.base zero))))
      (λa₁ apos ih b h₂, lt.cases_on h₂
        (lt.base a₁)
        (λ b₁ bpos,
          eq.rec_on (sub.succ_succ_symm a₁ b₁)
            (lt.trans (@ih b₁ bpos) (lt.base a₁)))),
  λ h₁ h₂, aux h₁ h₂

end nat
