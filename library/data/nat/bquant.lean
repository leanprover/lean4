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
import data.subtype data.nat.order data.nat.div

namespace nat
  open subtype

  definition bex [reducible] (n : nat) (P : nat → Prop) : Prop :=
  ∃ x, x < n ∧ P x

  definition bsub [reducible] (n : nat) (P : nat → Prop) : Type₁ :=
  {x | x < n ∧ P x}

  definition ball [reducible] (n : nat) (P : nat → Prop) : Prop :=
  ∀ x, x < n → P x

  lemma bex_of_bsub {n : nat} {P : nat → Prop} : bsub n P → bex n P :=
  assume h, ex_of_sub h

  theorem not_bex_zero (P : nat → Prop) : ¬ bex 0 P :=
  λ H, obtain (w : nat) (Hw : w < 0 ∧ P w), from H,
    and.rec_on Hw (λ h₁ h₂, absurd h₁ (not_lt_zero w))

  theorem not_bsub_zero (P : nat → Prop) : bsub 0 P → false :=
  λ H, absurd (bex_of_bsub H) (not_bex_zero P)

  definition bsub_succ {P : nat → Prop} {n : nat} (H : bsub n P) : bsub (succ n) P :=
  obtain (w : nat) (Hw : w < n ∧ P w), from H,
    and.rec_on Hw (λ hlt hp, tag w (and.intro (lt.step hlt) hp))

  theorem bex_succ {P : nat → Prop} {n : nat} (H : bex n P) : bex (succ n) P :=
  obtain (w : nat) (Hw : w < n ∧ P w), from H,
    and.rec_on Hw (λ hlt hp, exists.intro w (and.intro (lt.step hlt) hp))

  definition bsub_succ_of_pred {P : nat → Prop} {a : nat} (H : P a) : bsub (succ a) P :=
  tag a (and.intro (lt.base a) H)

  theorem bex_succ_of_pred {P : nat → Prop} {a : nat} (H : P a) : bex (succ a) P :=
  bex_of_bsub (bsub_succ_of_pred H)

  theorem not_bex_succ {P : nat → Prop} {n : nat} (H₁ : ¬ bex n P) (H₂ : ¬ P n) : ¬ bex (succ n) P :=
  λ H, obtain (w : nat) (Hw : w < succ n ∧ P w), from H,
    and.rec_on Hw (λ hltsn hp, or.rec_on (eq_or_lt_of_le (le_of_succ_le_succ hltsn))
      (λ heq : w = n, absurd (eq.rec_on heq hp) H₂)
      (λ hltn : w < n, absurd (exists.intro w (and.intro hltn hp)) H₁))

  theorem not_bsub_succ {P : nat → Prop} {n : nat} (H₁ : ¬ bex n P) (H₂ : ¬ P n) : bsub (succ n) P → false :=
  λ H, absurd (bex_of_bsub H) (not_bex_succ H₁ H₂)

  theorem ball_zero (P : nat → Prop) : ball zero P :=
  λ x Hlt, absurd Hlt !not_lt_zero

  theorem ball_of_ball_succ {n : nat} {P : nat → Prop} (H : ball (succ n) P) : ball n P  :=
  λ x Hlt, H x (lt.step Hlt)

  theorem ball_succ_of_ball {n : nat} {P : nat → Prop} (H₁ : ball n P) (H₂ : P n) : ball (succ n) P :=
  λ (x : nat) (Hlt : x < succ n), or.elim (eq_or_lt_of_le (le_of_succ_le_succ Hlt))
    (λ heq : x = n, eq.rec_on (eq.rec_on heq rfl) H₂)
    (λ hlt : x < n, H₁ x hlt)

  theorem not_ball_of_not {n : nat} {P : nat → Prop} (H₁ : ¬ P n) : ¬ ball (succ n) P :=
  λ (H : ball (succ n) P), absurd (H n (lt.base n)) H₁

  theorem not_ball_succ_of_not_ball {n : nat} {P : nat → Prop} (H₁ : ¬ ball n P) : ¬ ball (succ n) P :=
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

  definition decidable_bex_le [instance] (n : nat) (P : nat → Prop) [H : decidable_pred P]
    : decidable (∃ x, x ≤ n ∧ P x) :=
  decidable_of_decidable_of_iff
    (decidable_bex (succ n) P)
    (exists_congr (λn, and_iff_and !lt_succ_iff_le !iff.refl))

  definition decidable_ball_le [instance] (n : nat) (P : nat → Prop) [H : decidable_pred P]
    : decidable (∀ x, x ≤ n → P x) :=
  decidable_of_decidable_of_iff
    (decidable_ball (succ n) P)
    (forall_congr (λn, imp_iff_imp !lt_succ_iff_le !iff.refl))
end

namespace nat
  open decidable
  variable {P : nat → Prop}
  variable [decP : decidable_pred P]
  include decP

  definition bsub_not_of_not_ball : ∀ {n : nat}, ¬ ball n P → {i | i < n ∧ ¬ P i}
  | 0        h := absurd (ball_zero P) h
  | (succ n) h := decidable.by_cases
    (λ hp : P n,
      have ¬ ball n P, from
        assume b : ball n P, absurd (ball_succ_of_ball b hp) h,
      have {i | i < n ∧ ¬ P i}, from bsub_not_of_not_ball this,
      bsub_succ this)
    (λ hn : ¬ P n, bsub_succ_of_pred hn)

  theorem bex_not_of_not_ball {n : nat} (H : ¬ ball n P) : bex n (λ n, ¬ P n) :=
  bex_of_bsub (bsub_not_of_not_ball H)

  theorem ball_not_of_not_bex : ∀ {n : nat}, ¬ bex n P → ball n (λ n, ¬ P n)
  | 0        h := ball_zero _
  | (succ n) h := by_cases
    (λ hp : P n, absurd (bex_succ_of_pred hp) h)
    (λ hn : ¬ P n,
      have ¬ bex n P, from
        assume b : bex n P, absurd (bex_succ b) h,
      have ball n (λ n, ¬ P n), from ball_not_of_not_bex this,
      ball_succ_of_ball this hn)
end nat
