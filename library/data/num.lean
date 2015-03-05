/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: data.num
Author: Leonardo de Moura
-/
import data.bool
open bool eq.ops decidable

namespace pos_num
  theorem succ_not_is_one (a : pos_num) : is_one (succ a) = ff :=
  pos_num.induction_on a rfl (take n iH, rfl) (take n iH, rfl)

  theorem succ_one_eq_bit0_one : succ one = bit0 one :=
  rfl

  theorem succ_bit1_eq_bit0_succ (a : pos_num) : succ (bit1 a) = bit0 (succ a) :=
  rfl

  theorem succ_bit0_eq_bit1 (a : pos_num) : succ (bit0 a) = bit1 a :=
  rfl

  theorem ne_of_bit0_ne_bit0 {a b : pos_num} (H₁ : bit0 a ≠ bit0 b) : a ≠ b :=
  assume H : a = b,
  absurd rfl (H ▸ H₁)

  theorem ne_of_bit1_ne_bit1 {a b : pos_num} (H₁ : bit1 a ≠ bit1 b) : a ≠ b :=
  assume H : a = b,
  absurd rfl (H ▸ H₁)

  theorem pred_bit0_eq_cond (a : pos_num) : pred (bit0 a) = cond (is_one a) one (bit1 (pred a)) :=
  rfl

  theorem pred_succ : ∀ (a : pos_num), pred (succ a) = a
  | pred_succ one      := rfl
  | pred_succ (bit0 a) := by rewrite succ_bit0_eq_bit1
  | pred_succ (bit1 a) :=
      calc
        pred (succ (bit1 a)) = cond (is_one (succ a)) one (bit1 (pred (succ a))) : rfl
                       ...   = cond ff one (bit1 (pred (succ a)))                : succ_not_is_one
                       ...   = bit1 (pred (succ a))                              : rfl
                       ...   = bit1 a                                            : pred_succ a

  section
  variables (a b : pos_num)

  theorem add.one_one : one + one = bit0 one :=
  rfl

  theorem add.one_bit0 : one + (bit0 a) = bit1 a :=
  rfl

  theorem add.one_bit1 : one + (bit1 a) = succ (bit1 a) :=
  rfl

  theorem add.bit0_one : (bit0 a) + one = bit1 a :=
  rfl

  theorem add.bit1_one : (bit1 a) + one = succ (bit1 a) :=
  rfl

  theorem add.bit0_bit0 : (bit0 a) + (bit0 b) = bit0 (a + b) :=
  rfl

  theorem add.bit0_bit1 : (bit0 a) + (bit1 b) = bit1 (a + b) :=
  rfl

  theorem add.bit1_bit0 : (bit1 a) + (bit0 b) = bit1 (a + b) :=
  rfl

  theorem add.bit1_bit1 : (bit1 a) + (bit1 b) = succ (bit1 (a + b)) :=
  rfl
  end

  theorem mul.one_left (a : pos_num) : one * a = a :=
  rfl

  theorem mul.one_right (a : pos_num) : a * one = a :=
  pos_num.induction_on a
    rfl
    (take (n : pos_num) (iH : n * one = n),
      calc bit1 n * one = bit0 (n * one) + one : rfl
                   ...  = bit0 n + one         : iH
                   ...  = bit1 n               : add.bit0_one)
    (take (n : pos_num) (iH : n * one = n),
      calc bit0 n * one = bit0 (n * one)       : rfl
                    ... = bit0 n               : iH)

  theorem decidable_eq [instance] : ∀ (a b : pos_num), decidable (a = b)
  | decidable_eq one      one      := inl rfl
  | decidable_eq one      (bit0 b) := inr (λ H, pos_num.no_confusion H)
  | decidable_eq one      (bit1 b) := inr (λ H, pos_num.no_confusion H)
  | decidable_eq (bit0 a) one      := inr (λ H, pos_num.no_confusion H)
  | decidable_eq (bit0 a) (bit0 b) :=
    match decidable_eq a b with
    | inl H₁  := inl (eq.rec_on H₁ rfl)
    | inr H₁  := inr (λ H, pos_num.no_confusion H (λ H₂, absurd H₂ H₁))
    end
  | decidable_eq (bit0 a) (bit1 b) := inr (λ H, pos_num.no_confusion H)
  | decidable_eq (bit1 a) one      := inr (λ H, pos_num.no_confusion H)
  | decidable_eq (bit1 a) (bit0 b) := inr (λ H, pos_num.no_confusion H)
  | decidable_eq (bit1 a) (bit1 b) :=
    match decidable_eq a b with
    | inl H₁  := inl (eq.rec_on H₁ rfl)
    | inr H₁  := inr (λ H, pos_num.no_confusion H (λ H₂, absurd H₂ H₁))
    end

  local notation a < b         := (lt a b = tt)
  local notation a `≮`:50 b:50 := (lt a b = ff)

  theorem lt_one_right_eq_ff : ∀ a : pos_num, a ≮ one
  | lt_one_right_eq_ff one      := rfl
  | lt_one_right_eq_ff (bit0 a) := rfl
  | lt_one_right_eq_ff (bit1 a) := rfl

  theorem lt_one_succ_eq_tt : ∀ a : pos_num, one < succ a
  | lt_one_succ_eq_tt one      := rfl
  | lt_one_succ_eq_tt (bit0 a) := rfl
  | lt_one_succ_eq_tt (bit1 a) := rfl

  theorem lt_of_lt_bit0_bit0 {a b : pos_num} (H : bit0 a < bit0 b) : a < b := H
  theorem lt_of_lt_bit0_bit1 {a b : pos_num} (H : bit1 a < bit0 b) : a < b := H
  theorem lt_of_lt_bit1_bit1 {a b : pos_num} (H : bit1 a < bit1 b) : a < b := H
  theorem lt_of_lt_bit1_bit0 {a b : pos_num} (H : bit0 a < bit1 b) : a < succ b := H

  theorem lt_bit0_bit0_eq_lt (a b : pos_num) : lt (bit0 a) (bit0 b) = lt a b :=
  rfl

  theorem lt_bit1_bit1_eq_lt (a b : pos_num) : lt (bit1 a) (bit1 b) = lt a b :=
  rfl

  theorem lt_bit1_bit0_eq_lt (a b : pos_num) : lt (bit1 a) (bit0 b) = lt a b :=
  rfl

  theorem lt_bit0_bit1_eq_lt_succ (a b : pos_num) : lt (bit0 a) (bit1 b) = lt a (succ b) :=
  rfl

  theorem lt_irrefl : ∀ (a : pos_num), a ≮ a
  | lt_irrefl one      := rfl
  | lt_irrefl (bit0 a) :=
    begin
      rewrite lt_bit0_bit0_eq_lt, apply lt_irrefl
    end
  | lt_irrefl (bit1 a) :=
    begin
      rewrite lt_bit1_bit1_eq_lt, apply lt_irrefl
    end

  theorem ne_of_lt_eq_tt : ∀ {a b : pos_num}, a < b → a = b → false
  | @ne_of_lt_eq_tt one      ⌞one⌟      H₁ (eq.refl one)      := absurd H₁ ff_ne_tt
  | @ne_of_lt_eq_tt (bit0 a) ⌞(bit0 a)⌟ H₁ (eq.refl (bit0 a)) :=
    begin
      rewrite lt_bit0_bit0_eq_lt at H₁,
      apply (ne_of_lt_eq_tt H₁ (eq.refl a))
    end
  | @ne_of_lt_eq_tt (bit1 a) ⌞(bit1 a)⌟ H₁ (eq.refl (bit1 a)) :=
    begin
      rewrite lt_bit1_bit1_eq_lt at H₁,
      apply (ne_of_lt_eq_tt H₁ (eq.refl a))
    end

  theorem lt_base : ∀ a : pos_num, a < succ a
  | lt_base one      := rfl
  | lt_base (bit0 a) :=
    begin
      rewrite [succ_bit0_eq_bit1, lt_bit0_bit1_eq_lt_succ],
      apply lt_base
    end
  | lt_base (bit1 a) :=
    begin
      rewrite [succ_bit1_eq_bit0_succ, lt_bit1_bit0_eq_lt],
      apply lt_base
    end

  theorem lt_step : ∀ {a b : pos_num}, a < b → a < succ b
  | @lt_step one      one      H := rfl
  | @lt_step one      (bit0 b) H := rfl
  | @lt_step one      (bit1 b) H := rfl
  | @lt_step (bit0 a) one      H := absurd H ff_ne_tt
  | @lt_step (bit0 a) (bit0 b) H :=
    begin
      rewrite [succ_bit0_eq_bit1, lt_bit0_bit1_eq_lt_succ, lt_bit0_bit0_eq_lt at H],
      apply (lt_step H)
    end
  | @lt_step (bit0 a) (bit1 b) H :=
    begin
      rewrite [succ_bit1_eq_bit0_succ, lt_bit0_bit0_eq_lt, lt_bit0_bit1_eq_lt_succ at H],
      exact H
    end
  | @lt_step (bit1 a) one      H := absurd H ff_ne_tt
  | @lt_step (bit1 a) (bit0 b) H :=
    begin
      rewrite [succ_bit0_eq_bit1, lt_bit1_bit1_eq_lt, lt_bit1_bit0_eq_lt at H],
      exact H
    end
  | @lt_step (bit1 a) (bit1 b) H :=
    begin
      rewrite [succ_bit1_eq_bit0_succ, lt_bit1_bit0_eq_lt, lt_bit1_bit1_eq_lt at H],
      apply (lt_step H)
    end

  theorem lt_of_lt_succ_succ : ∀ {a b : pos_num}, succ a < succ b → a < b
  | @lt_of_lt_succ_succ one      one      H := absurd H ff_ne_tt
  | @lt_of_lt_succ_succ one      (bit0 b) H := rfl
  | @lt_of_lt_succ_succ one      (bit1 b) H := rfl
  | @lt_of_lt_succ_succ (bit0 a) one      H :=
    begin
      rewrite [succ_bit0_eq_bit1 at H, succ_one_eq_bit0_one at H, lt_bit1_bit0_eq_lt at H],
      apply (absurd_of_eq_ff_of_eq_tt (lt_one_right_eq_ff a) H)
    end
  | @lt_of_lt_succ_succ (bit0 a) (bit0 b) H := by exact H
  | @lt_of_lt_succ_succ (bit0 a) (bit1 b) H := by exact H
  | @lt_of_lt_succ_succ (bit1 a) one      H :=
    begin
      rewrite [succ_bit1_eq_bit0_succ at H, succ_one_eq_bit0_one at H, lt_bit0_bit0_eq_lt at H],
      apply (absurd_of_eq_ff_of_eq_tt (lt_one_right_eq_ff (succ a)) H)
    end
  | @lt_of_lt_succ_succ (bit1 a) (bit0 b) H :=
    begin
      rewrite [succ_bit1_eq_bit0_succ at H, succ_bit0_eq_bit1 at H, lt_bit0_bit1_eq_lt_succ at H],
      rewrite lt_bit1_bit0_eq_lt,
      apply (lt_of_lt_succ_succ H)
    end
  | @lt_of_lt_succ_succ (bit1 a) (bit1 b) H :=
    begin
      rewrite [lt_bit1_bit1_eq_lt, *succ_bit1_eq_bit0_succ at H, lt_bit0_bit0_eq_lt at H],
      apply (lt_of_lt_succ_succ H)
    end

  theorem lt_succ_succ : ∀ {a b : pos_num}, a < b → succ a < succ b
  | @lt_succ_succ one      one      H := absurd H ff_ne_tt
  | @lt_succ_succ one      (bit0 b) H :=
    begin
      rewrite [succ_bit0_eq_bit1, succ_one_eq_bit0_one, lt_bit0_bit1_eq_lt_succ],
      apply lt_one_succ_eq_tt
    end
  | @lt_succ_succ one      (bit1 b) H :=
    begin
      rewrite [succ_one_eq_bit0_one, succ_bit1_eq_bit0_succ, lt_bit0_bit0_eq_lt],
      apply lt_one_succ_eq_tt
    end
  | @lt_succ_succ (bit0 a) one      H := absurd H ff_ne_tt
  | @lt_succ_succ (bit0 a) (bit0 b) H := by exact H
  | @lt_succ_succ (bit0 a) (bit1 b) H := by exact H
  | @lt_succ_succ (bit1 a) one      H := absurd H ff_ne_tt
  | @lt_succ_succ (bit1 a) (bit0 b) H :=
    begin
      rewrite [succ_bit1_eq_bit0_succ, succ_bit0_eq_bit1, lt_bit0_bit1_eq_lt_succ, lt_bit1_bit0_eq_lt at H],
      apply (lt_succ_succ H)
    end
  | @lt_succ_succ (bit1 a) (bit1 b) H :=
    begin
      rewrite [lt_bit1_bit1_eq_lt at H, *succ_bit1_eq_bit0_succ, lt_bit0_bit0_eq_lt],
      apply (lt_succ_succ H)
    end

  theorem lt_of_lt_succ : ∀ {a b : pos_num}, succ a < b → a < b
  | @lt_of_lt_succ one      one      H := absurd_of_eq_ff_of_eq_tt !lt_one_right_eq_ff H
  | @lt_of_lt_succ one      (bit0 b) H := rfl
  | @lt_of_lt_succ one      (bit1 b) H := rfl
  | @lt_of_lt_succ (bit0 a) one      H := absurd_of_eq_ff_of_eq_tt !lt_one_right_eq_ff H
  | @lt_of_lt_succ (bit0 a) (bit0 b) H := by exact H
  | @lt_of_lt_succ (bit0 a) (bit1 b) H :=
    begin
      rewrite [succ_bit0_eq_bit1 at H, lt_bit1_bit1_eq_lt at H, lt_bit0_bit1_eq_lt_succ],
      apply (lt_step H)
    end
  | @lt_of_lt_succ (bit1 a) one      H := absurd_of_eq_ff_of_eq_tt !lt_one_right_eq_ff H
  | @lt_of_lt_succ (bit1 a) (bit0 b) H :=
    begin
      rewrite [lt_bit1_bit0_eq_lt, succ_bit1_eq_bit0_succ at H, lt_bit0_bit0_eq_lt at H],
      apply (lt_of_lt_succ H)
    end
  | @lt_of_lt_succ (bit1 a) (bit1 b) H :=
    begin
      rewrite [succ_bit1_eq_bit0_succ at H, lt_bit0_bit1_eq_lt_succ at H, lt_bit1_bit1_eq_lt],
      apply (lt_of_lt_succ_succ H)
    end

  theorem lt_of_lt_succ_of_ne : ∀ {a b : pos_num}, a < succ b → a ≠ b → a < b
  | @lt_of_lt_succ_of_ne one      one      H₁ H₂ := absurd rfl H₂
  | @lt_of_lt_succ_of_ne one      (bit0 b) H₁ H₂ := rfl
  | @lt_of_lt_succ_of_ne one      (bit1 b) H₁ H₂ := rfl
  | @lt_of_lt_succ_of_ne (bit0 a) one      H₁ H₂ :=
  begin
    rewrite [succ_one_eq_bit0_one at H₁, lt_bit0_bit0_eq_lt at H₁],
    apply (absurd_of_eq_ff_of_eq_tt (lt_one_right_eq_ff _) H₁)
  end
  | @lt_of_lt_succ_of_ne (bit0 a) (bit0 b) H₁ H₂ :=
    begin
      rewrite [lt_bit0_bit0_eq_lt, succ_bit0_eq_bit1 at H₁, lt_bit0_bit1_eq_lt_succ at H₁],
      apply (lt_of_lt_succ_of_ne H₁ (ne_of_bit0_ne_bit0 H₂))
    end
  | @lt_of_lt_succ_of_ne (bit0 a) (bit1 b) H₁ H₂ :=
    begin
      rewrite [succ_bit1_eq_bit0_succ at H₁, lt_bit0_bit0_eq_lt at H₁, lt_bit0_bit1_eq_lt_succ],
      exact H₁
    end
  | @lt_of_lt_succ_of_ne (bit1 a) one      H₁ H₂ :=
    begin
      rewrite [succ_one_eq_bit0_one at H₁, lt_bit1_bit0_eq_lt at H₁],
      apply (absurd_of_eq_ff_of_eq_tt (lt_one_right_eq_ff _) H₁)
    end
  | @lt_of_lt_succ_of_ne (bit1 a) (bit0 b) H₁ H₂ :=
    begin
      rewrite [succ_bit0_eq_bit1 at H₁, lt_bit1_bit1_eq_lt at H₁, lt_bit1_bit0_eq_lt],
      exact H₁
    end
  | @lt_of_lt_succ_of_ne (bit1 a) (bit1 b) H₁ H₂ :=
    begin
      rewrite [succ_bit1_eq_bit0_succ at H₁, lt_bit1_bit0_eq_lt at H₁, lt_bit1_bit1_eq_lt],
      apply (lt_of_lt_succ_of_ne H₁ (ne_of_bit1_ne_bit1 H₂))
    end

  theorem lt_trans : ∀ {a b c : pos_num}, a < b → b < c → a < c
  | @lt_trans one      b        (bit0 c) H₁ H₂ := rfl
  | @lt_trans one      b        (bit1 c) H₁ H₂ := rfl
  | @lt_trans a        (bit0 b) one      H₁ H₂ := absurd_of_eq_ff_of_eq_tt (lt_one_right_eq_ff _) H₂
  | @lt_trans a        (bit1 b) one      H₁ H₂ := absurd_of_eq_ff_of_eq_tt (lt_one_right_eq_ff _) H₂
  | @lt_trans (bit0 a) (bit0 b) (bit0 c) H₁ H₂ :=
    begin
      rewrite lt_bit0_bit0_eq_lt at *, apply (lt_trans H₁ H₂)
    end
  | @lt_trans (bit0 a) (bit0 b) (bit1 c) H₁ H₂ :=
    begin
      rewrite [lt_bit0_bit1_eq_lt_succ at *, lt_bit0_bit0_eq_lt at H₁],
      apply (lt_trans H₁ H₂)
    end
  | @lt_trans (bit0 a) (bit1 b) (bit0 c) H₁ H₂ :=
    begin
      rewrite [lt_bit0_bit1_eq_lt_succ at H₁, lt_bit1_bit0_eq_lt at H₂, lt_bit0_bit0_eq_lt],
      apply (@by_cases (a = b)),
      begin
         intro H, rewrite -H at H₂, exact H₂
      end,
      begin
        intro H,
        apply (lt_trans (lt_of_lt_succ_of_ne H₁ H) H₂)
      end
    end
  | @lt_trans (bit0 a) (bit1 b) (bit1 c) H₁ H₂ :=
    begin
      rewrite [lt_bit0_bit1_eq_lt_succ at *, lt_bit1_bit1_eq_lt at H₂],
      apply (lt_trans H₁ (lt_succ_succ H₂))
    end
  | @lt_trans (bit1 a) (bit0 b) (bit0 c) H₁ H₂ :=
    begin
      rewrite [lt_bit0_bit0_eq_lt at H₂, lt_bit1_bit0_eq_lt at *],
      apply (lt_trans H₁ H₂)
    end
  | @lt_trans (bit1 a) (bit0 b) (bit1 c) H₁ H₂ :=
    begin
      rewrite [lt_bit1_bit0_eq_lt at H₁, lt_bit0_bit1_eq_lt_succ at H₂, lt_bit1_bit1_eq_lt],
      apply (@by_cases (b = c)),
      begin
        intro H, rewrite H at H₁, exact H₁
      end,
      begin
        intro H,
        apply (lt_trans H₁ (lt_of_lt_succ_of_ne H₂ H))
      end
    end
  | @lt_trans (bit1 a) (bit1 b) (bit0 c) H₁ H₂ :=
    begin
      rewrite [lt_bit1_bit1_eq_lt at H₁, lt_bit1_bit0_eq_lt at H₂, lt_bit1_bit0_eq_lt],
      apply (lt_trans H₁ H₂)
    end
  | @lt_trans (bit1 a) (bit1 b) (bit1 c) H₁ H₂ :=
    begin
      rewrite lt_bit1_bit1_eq_lt at *,
      apply (lt_trans H₁ H₂)
    end

  theorem lt_antisymm : ∀ {a b : pos_num}, a < b → b ≮ a
  | @lt_antisymm one      one      H := rfl
  | @lt_antisymm one      (bit0 b) H := rfl
  | @lt_antisymm one      (bit1 b) H := rfl
  | @lt_antisymm (bit0 a) one      H := absurd H ff_ne_tt
  | @lt_antisymm (bit0 a) (bit0 b) H :=
    begin
      rewrite lt_bit0_bit0_eq_lt at *,
      apply (lt_antisymm H)
    end
  | @lt_antisymm (bit0 a) (bit1 b) H :=
    begin
      rewrite lt_bit1_bit0_eq_lt,
      rewrite lt_bit0_bit1_eq_lt_succ at H,
      have H₁ : succ b ≮ a, from lt_antisymm H,
      apply eq_ff_of_ne_tt,
        intro H₂,
        apply (@by_cases (succ b = a)),
        show succ b = a → false,
        begin
          intro Hp,
          rewrite -Hp at H,
          apply (absurd_of_eq_ff_of_eq_tt (lt_irrefl (succ b)) H)
        end,
        show succ b ≠ a → false,
        begin
          intro Hn,
          have H₃ : succ b < succ a, from lt_succ_succ H₂,
          have H₄ : succ b < a, from lt_of_lt_succ_of_ne H₃ Hn,
          apply (absurd_of_eq_ff_of_eq_tt H₁ H₄)
        end,
    end
  | @lt_antisymm (bit1 a) one      H := absurd H ff_ne_tt
  | @lt_antisymm (bit1 a) (bit0 b) H :=
    begin
      rewrite lt_bit0_bit1_eq_lt_succ,
      rewrite lt_bit1_bit0_eq_lt at H,
      have H₁ : lt b a = ff, from lt_antisymm H,
      apply eq_ff_of_ne_tt,
        intro H₂,
        apply (@by_cases (b = a)),
        show b = a → false,
        begin
          intro Hp,
          rewrite -Hp at H,
          apply (absurd_of_eq_ff_of_eq_tt (lt_irrefl b) H)
        end,
        show b ≠ a → false,
        begin
          intro Hn,
          have H₃ : b < a, from lt_of_lt_succ_of_ne H₂ Hn,
          apply (absurd_of_eq_ff_of_eq_tt H₁ H₃)
        end,
      end
  | @lt_antisymm (bit1 a) (bit1 b) H :=
    begin
      rewrite lt_bit1_bit1_eq_lt at *,
      apply (lt_antisymm H)
    end

  local notation a ≤ b := (le a b = tt)

  theorem le_refl : ∀ a : pos_num, a ≤ a :=
  lt_base

  theorem le_eq_lt_succ {a b : pos_num} : le a b = lt a (succ b) :=
  rfl

  theorem not_lt_of_le : ∀ {a b : pos_num}, a ≤ b → b < a → false
  | @not_lt_of_le one      one      H₁ H₂ := absurd H₂ ff_ne_tt
  | @not_lt_of_le one      (bit0 b) H₁ H₂ := absurd_of_eq_ff_of_eq_tt (lt_one_right_eq_ff _) H₂
  | @not_lt_of_le one      (bit1 b) H₁ H₂ := absurd_of_eq_ff_of_eq_tt (lt_one_right_eq_ff _) H₂
  | @not_lt_of_le (bit0 a) one      H₁ H₂ :=
    begin
      rewrite [le_eq_lt_succ at H₁, succ_one_eq_bit0_one at H₁, lt_bit0_bit0_eq_lt at H₁],
      apply (absurd_of_eq_ff_of_eq_tt (lt_one_right_eq_ff _) H₁)
    end
  | @not_lt_of_le (bit0 a) (bit0 b) H₁ H₂ :=
    begin
      rewrite [le_eq_lt_succ at H₁, succ_bit0_eq_bit1 at H₁, lt_bit0_bit1_eq_lt_succ at H₁],
      rewrite [lt_bit0_bit0_eq_lt at H₂],
      apply (not_lt_of_le H₁ H₂)
    end
  | @not_lt_of_le (bit0 a) (bit1 b) H₁ H₂ :=
    begin
      rewrite [le_eq_lt_succ at H₁, succ_bit1_eq_bit0_succ at H₁, lt_bit0_bit0_eq_lt at H₁],
      rewrite [lt_bit1_bit0_eq_lt at H₂],
      apply (not_lt_of_le H₁ H₂)
    end
  | @not_lt_of_le (bit1 a) one      H₁ H₂ :=
    begin
      rewrite [le_eq_lt_succ at H₁, succ_one_eq_bit0_one at H₁, lt_bit1_bit0_eq_lt at H₁],
      apply (absurd_of_eq_ff_of_eq_tt (lt_one_right_eq_ff _) H₁)
    end
  | @not_lt_of_le (bit1 a) (bit0 b) H₁ H₂ :=
    begin
      rewrite [le_eq_lt_succ at H₁, succ_bit0_eq_bit1 at H₁, lt_bit1_bit1_eq_lt at H₁],
      rewrite lt_bit0_bit1_eq_lt_succ at H₂,
      have H₃ : a < succ b, from lt_step H₁,
      apply (@by_cases (b = a)),
      begin
        intro Hba, rewrite -Hba at H₁,
        apply (absurd_of_eq_ff_of_eq_tt (lt_irrefl b) H₁)
      end,
      begin
        intro Hnba,
        have H₄ : b < a, from lt_of_lt_succ_of_ne H₂ Hnba,
        apply (not_lt_of_le H₃ H₄)
      end
    end
  | @not_lt_of_le (bit1 a) (bit1 b) H₁ H₂ :=
    begin
      rewrite [le_eq_lt_succ at H₁, succ_bit1_eq_bit0_succ at H₁, lt_bit1_bit0_eq_lt at H₁],
      rewrite [lt_bit1_bit1_eq_lt at H₂],
      apply (not_lt_of_le H₁ H₂)
    end

  theorem le_antisymm : ∀ {a b : pos_num}, a ≤ b → b ≤ a → a = b
  | @le_antisymm one      one      H₁ H₂ := rfl
  | @le_antisymm one      (bit0 b) H₁ H₂ :=
    by apply (absurd_of_eq_ff_of_eq_tt (lt_one_right_eq_ff b) H₂)
  | @le_antisymm one      (bit1 b) H₁ H₂ :=
    by apply (absurd_of_eq_ff_of_eq_tt (lt_one_right_eq_ff b) H₂)
  | @le_antisymm (bit0 a) one      H₁ H₂ :=
    by apply (absurd_of_eq_ff_of_eq_tt (lt_one_right_eq_ff a) H₁)
  | @le_antisymm (bit0 a) (bit0 b) H₁ H₂ :=
    begin
      rewrite [le_eq_lt_succ at *, succ_bit0_eq_bit1 at *, lt_bit0_bit1_eq_lt_succ at *],
      have H : a = b, from le_antisymm H₁ H₂,
      rewrite H
    end
  | @le_antisymm (bit0 a) (bit1 b) H₁ H₂ :=
    begin
      rewrite [le_eq_lt_succ at *, succ_bit1_eq_bit0_succ at H₁, succ_bit0_eq_bit1 at H₂],
      rewrite [lt_bit0_bit0_eq_lt at H₁, lt_bit1_bit1_eq_lt at H₂],
      apply (false.rec _ (not_lt_of_le H₁ H₂))
    end
  | @le_antisymm (bit1 a) one      H₁ H₂ :=
    by apply (absurd_of_eq_ff_of_eq_tt (lt_one_right_eq_ff a) H₁)
  | @le_antisymm (bit1 a) (bit0 b) H₁ H₂ :=
    begin
      rewrite [le_eq_lt_succ at *, succ_bit0_eq_bit1 at H₁, succ_bit1_eq_bit0_succ at H₂],
      rewrite [lt_bit1_bit1_eq_lt at H₁, lt_bit0_bit0_eq_lt at H₂],
      apply (false.rec _ (not_lt_of_le H₂ H₁))
    end
  | @le_antisymm (bit1 a) (bit1 b) H₁ H₂ :=
    begin
      rewrite [le_eq_lt_succ at *, succ_bit1_eq_bit0_succ at *, lt_bit1_bit0_eq_lt at *],
      have H : a = b, from le_antisymm H₁ H₂,
      rewrite H
    end

  theorem le_trans {a b c : pos_num} : a ≤ b → b ≤ c → a ≤ c :=
  begin
    intros (H₁, H₂),
    rewrite [le_eq_lt_succ at *],
    apply (@by_cases (a = b)),
    begin
      intro Hab, rewrite Hab, exact H₂
    end,
    begin
      intro Hnab,
      have Haltb : a < b, from lt_of_lt_succ_of_ne H₁ Hnab,
      apply (lt_trans Haltb H₂)
    end,
  end

end pos_num
