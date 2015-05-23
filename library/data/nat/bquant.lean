/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura

Show that "bounded" quantifiers: (∃x, x < n ∧ P x) and (∀x, x < n → P x)
are decidable when P is decidable.

This module allow us to write if-then-else expressions such as

  if (∀ x : nat, x < n → ∃ y : nat, y < n ∧ y * y = x) then t else s

without assuming classical axioms.

More importantly, they can be reduced inside of the Lean kernel.
-/
import data.nat.order

namespace nat
  definition bex [reducible] (n : nat) (P : nat → Prop) : Prop :=
  ∃ x, x < n ∧ P x

  definition ball [reducible] (n : nat) (P : nat → Prop) : Prop :=
  ∀ x, x < n → P x

  definition not_bex_zero (P : nat → Prop) : ¬ bex 0 P :=
  λ H, obtain (w : nat) (Hw : w < 0 ∧ P w), from H,
    and.rec_on Hw (λ h₁ h₂, absurd h₁ (not_lt_zero w))

  definition bex_succ {P : nat → Prop} {n : nat} (H : bex n P) : bex (succ n) P :=
  obtain (w : nat) (Hw : w < n ∧ P w), from H,
    and.rec_on Hw (λ hlt hp, exists.intro w (and.intro (lt.step hlt) hp))

  definition bex_succ_of_pred {P : nat → Prop} {a : nat} (H : P a) : bex (succ a) P :=
  exists.intro a (and.intro (lt.base a) H)

  definition not_bex_succ {P : nat → Prop} {n : nat} (H₁ : ¬ bex n P) (H₂ : ¬ P n) : ¬ bex (succ n) P :=
  λ H, obtain (w : nat) (Hw : w < succ n ∧ P w), from H,
    and.rec_on Hw (λ hltsn hp, or.rec_on (eq_or_lt_of_le hltsn)
      (λ heq : w = n, absurd (eq.rec_on heq hp) H₂)
      (λ hltn : w < n, absurd (exists.intro w (and.intro hltn hp)) H₁))

  definition ball_zero (P : nat → Prop) : ball zero P :=
  λ x Hlt, absurd Hlt !not_lt_zero

  definition ball_of_ball_succ {n : nat} {P : nat → Prop} (H : ball (succ n) P) : ball n P  :=
  λ x Hlt, H x (lt.step Hlt)

  definition ball_succ_of_ball {n : nat} {P : nat → Prop} (H₁ : ball n P) (H₂ : P n) : ball (succ n) P :=
  λ (x : nat) (Hlt : x < succ n), or.elim (eq_or_lt_of_le Hlt)
    (λ heq : x = n, eq.rec_on (eq.rec_on heq rfl) H₂)
    (λ hlt : x < n, H₁ x hlt)

  definition not_ball_of_not {n : nat} {P : nat → Prop} (H₁ : ¬ P n) : ¬ ball (succ n) P :=
  λ (H : ball (succ n) P), absurd (H n (lt.base n)) H₁

  definition not_ball_succ_of_not_ball {n : nat} {P : nat → Prop} (H₁ : ¬ ball n P) : ¬ ball (succ n) P :=
  λ (H : ball (succ n) P), absurd (ball_of_ball_succ H) H₁
end nat

section
  open nat decidable

  definition decidable_bex [instance] (n : nat) (P : nat → Prop) [H : decidable_pred P] : decidable (bex n P) :=
  nat.rec_on n
    (inr (not_bex_zero P))
    (λ a ih, decidable.rec_on ih
      (λ hpos : bex a P, inl (bex_succ hpos))
      (λ hneg : ¬ bex a P, decidable.rec_on (H a)
         (λ hpa : P a, inl (bex_succ_of_pred hpa))
         (λ hna : ¬ P a, inr (not_bex_succ hneg hna))))

  definition decidable_ball [instance] (n : nat) (P : nat → Prop) [H : decidable_pred P] : decidable (ball n P) :=
  nat.rec_on n
    (inl (ball_zero P))
    (λ n₁ ih, decidable.rec_on ih
      (λ ih_pos, decidable.rec_on (H n₁)
        (λ p_pos, inl (ball_succ_of_ball ih_pos p_pos))
        (λ p_neg, inr (not_ball_of_not p_neg)))
      (λ ih_neg, inr (not_ball_succ_of_not_ball ih_neg)))
end
