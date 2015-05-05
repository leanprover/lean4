/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: init.nat
Authors: Floris van Doorn, Leonardo de Moura
-/
prelude
import init.wf init.tactic init.hedberg init.util init.types

open eq decidable sum lift

namespace nat
  notation `ℕ` := nat

  inductive lt (a : nat) : nat → Type₀ :=
  | base : lt a (succ a)
  | step : Π {b}, lt a b → lt a (succ b)

  notation a < b := lt a b

  definition le [reducible] (a b : nat) : Type₀ := a < succ b

  notation a ≤ b := le a b

  definition pred (a : nat) : nat :=
  nat.cases_on a zero (λ a₁, a₁)

  protected definition is_inhabited [instance] : inhabited nat :=
  inhabited.mk zero

  protected definition has_decidable_eq [instance] : ∀ x y : nat, decidable (x = y)
  | has_decidable_eq zero     zero     := inl rfl
  | has_decidable_eq (succ x) zero     := inr (by contradiction)
  | has_decidable_eq zero     (succ y) := inr (by contradiction)
  | has_decidable_eq (succ x) (succ y) :=
      match has_decidable_eq x y with
      | inl xeqy := inl (by rewrite xeqy)
      | inr xney := inr (λ h : succ x = succ y, by injection h with xeqy; exact absurd xeqy xney)
      end

  -- less-than is well-founded
  definition lt.wf [instance] : well_founded lt :=
  well_founded.intro (λn, nat.rec_on n
    (acc.intro zero (λ (y : nat) (hlt : y < zero),
      have aux : ∀ {n₁}, y < n₁ → zero = n₁ → acc lt y, from
        λ n₁ hlt, nat.lt.cases_on hlt
          (by contradiction)
          (by contradiction),
      aux hlt rfl))
    (λ (n : nat) (ih : acc lt n),
      acc.intro (succ n) (λ (m : nat) (hlt : m < succ n),
        have aux : ∀ {n₁} (hlt : m < n₁), succ n = n₁ → acc lt m, from
          λ n₁ hlt, nat.lt.cases_on hlt
            (λ (sn_eq_sm : succ n = succ m),
               by injection sn_eq_sm with neqm; rewrite neqm at ih; exact ih)
            (λ b (hlt : m < b) (sn_eq_sb : succ n = succ b),
               by injection sn_eq_sb with neqb; rewrite neqb at ih; exact acc.inv ih hlt),
        aux hlt rfl)))

  definition measure {A : Type} (f : A → nat) : A → A → Type₀ :=
  inv_image lt f

  definition measure.wf {A : Type} (f : A → nat) : well_founded (measure f) :=
  inv_image.wf f lt.wf

  definition not_lt_zero (a : nat) : ¬ a < zero :=
  have aux : Π {b}, a < b → b = zero → empty, from
    λ b H, lt.cases_on H
      (by contradiction)
      (by contradiction),
  λ H, aux H rfl

  definition zero_lt_succ (a : nat) : zero < succ a :=
  nat.rec_on a
    (lt.base zero)
    (λ a (hlt : zero < succ a), lt.step hlt)

  definition lt.trans [trans] {a b c : nat} (H₁ : a < b) (H₂ : b < c) : a < c :=
  have aux : a < b → a < c, from
    lt.rec_on H₂
      (λ h₁, lt.step h₁)
      (λ b₁ bb₁ ih h₁, lt.step (ih h₁)),
  aux H₁

  definition succ_lt_succ {a b : nat} (H : a < b) : succ a < succ b :=
  lt.rec_on H
    (lt.base (succ a))
    (λ b hlt ih, lt.trans ih (lt.base (succ b)))

  definition lt_of_succ_lt {a b : nat} (H : succ a < b) : a < b :=
  lt.rec_on H
    (lt.step (lt.base a))
    (λ b h ih, lt.step ih)

  definition lt_of_succ_lt_succ {a b : nat} (H : succ a < succ b) : a < b :=
  have aux : pred (succ a) < pred (succ b), from
    lt.rec_on H
      (lt.base a)
      (λ (b : nat) (hlt : succ a < b) ih,
        show pred (succ a) < pred (succ b), from
        lt_of_succ_lt hlt),
  aux

  definition decidable_lt [instance] : decidable_rel lt :=
  λ a b, nat.rec_on b
    (λ (a : nat), inr (not_lt_zero a))
    (λ (b₁ : nat) (ih : Π a, decidable (a < b₁)) (a : nat), nat.cases_on a
       (inl !zero_lt_succ)
       (λ a, decidable.rec_on (ih a)
         (λ h_pos : a < b₁, inl (succ_lt_succ h_pos))
         (λ h_neg : ¬ a < b₁,
           have aux : ¬ succ a < succ b₁, from
             λ h : succ a < succ b₁, h_neg (lt_of_succ_lt_succ h),
           inr aux)))
    a

  definition le.refl (a : nat) : a ≤ a :=
  lt.base a

  definition le_of_lt {a b : nat} (H : a < b) : a ≤ b :=
  lt.step H

  definition eq_or_lt_of_le {a b : nat} (H : a ≤ b) : a = b ⊎ a < b :=
  begin
    cases H with b hlt,
      apply sum.inl rfl,
      apply sum.inr hlt
  end

  definition le_of_eq_or_lt {a b : nat} (H : a = b ⊎ a < b) : a ≤ b :=
  sum.rec_on H
    (λ hl, eq.rec_on hl !le.refl)
    (λ hr, le_of_lt hr)

  definition decidable_le [instance] : decidable_rel le :=
  λ a b, decidable_iff_equiv _ (iff.intro le_of_eq_or_lt eq_or_lt_of_le)

  definition le.rec_on {a : nat} {P : nat → Type} {b : nat} (H : a ≤ b) (H₁ : P a) (H₂ : Π b, a < b → P b) : P b :=
  begin
    cases H with b hlt,
      apply H₁,
      apply H₂ b hlt
  end

  definition lt.irrefl (a : nat) : ¬ a < a :=
  nat.rec_on a
    !not_lt_zero
    (λ (a : nat) (ih : ¬ a < a) (h : succ a < succ a),
      ih (lt_of_succ_lt_succ h))

  definition lt.asymm {a b : nat} (H : a < b) : ¬ b < a :=
  lt.rec_on H
    (λ h : succ a < a, !lt.irrefl (lt_of_succ_lt h))
    (λ b hlt (ih : ¬ b < a) (h : succ b < a), ih (lt_of_succ_lt h))

  definition lt.trichotomy (a b : nat) : a < b ⊎ a = b ⊎ b < a :=
  nat.rec_on b
    (λa, nat.cases_on a
       (sum.inr (sum.inl rfl))
       (λ a₁, sum.inr (sum.inr !zero_lt_succ)))
    (λ b₁ (ih : Πa, a < b₁ ⊎ a = b₁ ⊎ b₁ < a) (a : nat), nat.cases_on a
       (sum.inl !zero_lt_succ)
       (λ a, sum.rec_on (ih a)
           (λ h : a < b₁, sum.inl (succ_lt_succ h))
           (λ h, sum.rec_on h
              (λ h : a = b₁, sum.inr (sum.inl (eq.rec_on h rfl)))
              (λ h : b₁ < a, sum.inr (sum.inr (succ_lt_succ h))))))
    a

  definition eq_or_lt_of_not_lt {a b : nat} (hnlt : ¬ a < b) : a = b ⊎ b < a :=
  sum.rec_on (lt.trichotomy a b)
    (λ hlt, absurd hlt hnlt)
    (λ h, h)

  definition lt_succ_of_le {a b : nat} (h : a ≤ b) : a < succ b :=
  h

  definition lt_of_succ_le {a b : nat} (h : succ a ≤ b) : a < b :=
  lt_of_succ_lt_succ h

  definition le_succ_of_le {a b : nat} (h : a ≤ b) : a ≤ succ b :=
  lt.step h

  definition succ_le_of_lt {a b : nat} (h : a < b) : succ a ≤ b :=
  succ_lt_succ h

  definition le.trans [trans] {a b c : nat} (h₁ : a ≤ b) (h₂ : b ≤ c) : a ≤ c :=
  begin
    cases h₁ with b' hlt,
      apply h₂,
      apply lt.trans hlt h₂
  end

  definition lt_of_le_of_lt [trans] {a b c : nat} (h₁ : a ≤ b) (h₂ : b < c) : a < c :=
  begin
    cases h₁ with b' hlt,
      apply h₂,
      apply lt.trans hlt h₂
  end

  definition lt_of_lt_of_le [trans] {a b c : nat} (h₁ : a < b) (h₂ : b ≤ c) : a < c :=
  begin
    cases h₁ with b' hlt,
      apply lt_of_succ_lt_succ h₂,
      apply lt.trans hlt (lt_of_succ_lt_succ h₂)
  end

  definition max (a b : nat) : nat :=
  if a < b then b else a

  definition min (a b : nat) : nat :=
  if a < b then a else b

  definition max_self (a : nat) : max a a = a :=
  eq.rec_on !if_t_t rfl

  definition max_eq_right {a b : nat} (H : a < b) : max a b = b :=
  if_pos H

  definition max_eq_left {a b : nat} (H : ¬ a < b) : max a b = a :=
  if_neg H

  definition eq_max_right {a b : nat} (H : a < b) : b = max a b :=
  eq.rec_on (max_eq_right H) rfl

  definition eq_max_left {a b : nat} (H : ¬ a < b) : a = max a b :=
  eq.rec_on (max_eq_left H) rfl

  definition le_max_left (a b : nat) : a ≤ max a b :=
  by_cases
    (λ h : a < b,   le_of_lt (eq.rec_on (eq_max_right h) h))
    (λ h : ¬ a < b, eq.rec_on (eq_max_left h) !le.refl)

  definition le_max_right (a b : nat) : b ≤ max a b :=
  by_cases
    (λ h : a < b,   eq.rec_on (eq_max_right h) !le.refl)
    (λ h : ¬ a < b, sum.rec_on (eq_or_lt_of_not_lt h)
      (λ heq, eq.rec_on heq (eq.rec_on (inverse (max_self a)) !le.refl))
      (λ h : b < a,
        have aux : a = max a b, from eq_max_left (lt.asymm h),
        eq.rec_on aux (le_of_lt h)))

  definition gt [reducible] a b := lt b a
  definition decidable_gt [instance] : decidable_rel gt :=
  _

  notation a > b := gt a b

  definition ge [reducible] a b := le b a
  definition decidable_ge [instance] : decidable_rel ge :=
  _

  notation a ≥ b := ge a b

  -- add is defined in init.num

  definition sub (a b : nat) : nat :=
  nat.rec_on b a (λ b₁ r, pred r)

  notation a - b := sub a b

  definition mul (a b : nat) : nat :=
  nat.rec_on b zero (λ b₁ r, r + a)

  notation a * b := mul a b

  section
  local attribute sub [reducible]
  definition succ_sub_succ_eq_sub (a b : nat) : succ a - succ b = a - b :=
  nat.rec_on b
    rfl
    (λ b₁ (ih : succ a - succ b₁ = a - b₁),
      eq.rec_on ih (eq.refl (pred (succ a - succ b₁))))
  end

  definition sub_eq_succ_sub_succ (a b : nat) : a - b = succ a - succ b :=
  eq.rec_on (succ_sub_succ_eq_sub a b) rfl

  definition zero_sub_eq_zero (a : nat) : zero - a = zero :=
  nat.rec_on a
    rfl
    (λ a₁ (ih : zero - a₁ = zero), ap pred ih)

  definition zero_eq_zero_sub (a : nat) : zero = zero - a :=
  eq.rec_on (zero_sub_eq_zero a) rfl

  definition sub_lt {a b : nat} : zero < a → zero < b → a - b < a :=
  have aux : Π {a}, zero < a → Π {b}, zero < b → a - b < a, from
    λa h₁, lt.rec_on h₁
      (λb h₂, lt.cases_on h₂
        (lt.base zero)
        (λ b₁ bpos,
          eq.rec_on (sub_eq_succ_sub_succ zero b₁)
           (eq.rec_on (zero_eq_zero_sub b₁) (lt.base zero))))
      (λa₁ apos ih b h₂, lt.cases_on h₂
        (lt.base a₁)
        (λ b₁ bpos,
          eq.rec_on (sub_eq_succ_sub_succ a₁ b₁)
            (lt.trans (@ih b₁ bpos) (lt.base a₁)))),
  λ h₁ h₂, aux h₁ h₂

  definition pred_le (a : nat) : pred a ≤ a :=
  nat.cases_on a
    (le.refl zero)
    (λ a₁, le_of_lt (lt.base a₁))

  definition sub_le (a b : nat) : a - b ≤ a :=
  nat.rec_on b
    (le.refl a)
    (λ b₁ ih, le.trans !pred_le ih)

end nat
