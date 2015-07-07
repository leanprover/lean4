/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura
-/
prelude
import init.wf init.tactic init.hedberg init.util init.types

open eq decidable sum lift is_trunc

namespace nat
  notation `ℕ` := nat

  /- basic definitions on natural numbers -/
  inductive le (a : ℕ) : ℕ → Type₀ :=
  | refl : le a a
  | step : Π {b}, le a b → le a (succ b)

  infix `≤` := le
  attribute le.refl [refl]

  definition lt [reducible] (n m : ℕ) := succ n ≤ m
  definition ge [reducible] (n m : ℕ) := m ≤ n
  definition gt [reducible] (n m : ℕ) := succ m ≤ n
  infix `<` := lt
  infix `≥` := ge
  infix `>` := gt

  definition pred [unfold 1] (a : nat) : nat :=
  nat.cases_on a zero (λ a₁, a₁)

  -- add is defined in init.num

  definition sub (a b : nat) : nat :=
  nat.rec_on b a (λ b₁ r, pred r)

  definition mul (a b : nat) : nat :=
  nat.rec_on b zero (λ b₁ r, r + a)

  notation a - b := sub a b
  notation a * b := mul a b


  /- properties of ℕ -/

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

  /- properties of inequality -/

  definition le_of_eq {n m : ℕ} (p : n = m) : n ≤ m := p ▸ le.refl n

  definition le_succ (n : ℕ) : n ≤ succ n := by repeat constructor

  definition pred_le (n : ℕ) : pred n ≤ n := by cases n;all_goals (repeat constructor)

  definition le.trans [trans] {n m k : ℕ} (H1 : n ≤ m) (H2 : m ≤ k) : n ≤ k :=
  by induction H2 with n H2 IH;exact H1;exact le.step IH

  definition le_succ_of_le {n m : ℕ} (H : n ≤ m) : n ≤ succ m := le.trans H !le_succ

  definition le_of_succ_le {n m : ℕ} (H : succ n ≤ m) : n ≤ m := le.trans !le_succ H

  definition le_of_lt {n m : ℕ} (H : n < m) : n ≤ m := le_of_succ_le H

  definition succ_le_succ [unfold 3] {n m : ℕ} (H : n ≤ m) : succ n ≤ succ m :=
  by induction H;reflexivity;exact le.step v_0

  definition pred_le_pred [unfold 3] {n m : ℕ} (H : n ≤ m) : pred n ≤ pred m :=
  by induction H;reflexivity;cases b;exact v_0;exact le.step v_0

  definition le_of_succ_le_succ [unfold 3] {n m : ℕ} (H : succ n ≤ succ m) : n ≤ m :=
  pred_le_pred H

  definition le_succ_of_pred_le [unfold 1] {n m : ℕ} (H : pred n ≤ m) : n ≤ succ m :=
  by cases n;exact le.step H;exact succ_le_succ H

  definition not_succ_le_self {n : ℕ} : ¬succ n ≤ n :=
  by induction n with n IH;all_goals intros;cases a;apply IH;exact le_of_succ_le_succ a

  definition zero_le (n : ℕ) : 0 ≤ n :=
  by induction n with n IH;apply le.refl;exact le.step IH

  definition lt.step {n m : ℕ} (H : n < m) : n < succ m :=
  le.step H

  definition zero_lt_succ (n : ℕ) : 0 < succ n :=
  by induction n with n IH;apply le.refl;exact le.step IH

  definition lt.trans [trans] {n m k : ℕ} (H1 : n < m) (H2 : m < k) : n < k :=
  le.trans (le.step H1) H2

  definition lt_of_le_of_lt [trans] {n m k : ℕ} (H1 : n ≤ m) (H2 : m < k) : n < k :=
  le.trans (succ_le_succ H1) H2

  definition lt_of_lt_of_le [trans] {n m k : ℕ} (H1 : n < m) (H2 : m ≤ k) : n < k :=
  le.trans H1 H2

  definition le.antisymm {n m : ℕ} (H1 : n ≤ m) (H2 : m ≤ n) : n = m :=
  begin
    cases H1 with m' H1',
    { reflexivity},
    { cases H2 with n' H2',
      { reflexivity},
      { exfalso, apply not_succ_le_self, exact lt.trans H1' H2'}},
  end

  definition not_succ_le_zero (n : ℕ) : ¬succ n ≤ zero :=
  by intro H; cases H

  definition lt.irrefl (n : ℕ) : ¬n < n := not_succ_le_self

  definition self_lt_succ (n : ℕ) : n < succ n := !le.refl
  definition lt.base (n : ℕ) : n < succ n := !le.refl

  definition le_lt_antisymm {n m : ℕ} (H1 : n ≤ m) (H2 : m < n) : empty :=
  !lt.irrefl (lt_of_le_of_lt H1 H2)

  definition lt_le_antisymm {n m : ℕ} (H1 : n < m) (H2 : m ≤ n) : empty :=
  le_lt_antisymm H2 H1

  definition lt.asymm {n m : ℕ} (H1 : n < m) (H2 : m < n) : empty :=
  le_lt_antisymm (le_of_lt H1) H2

  definition lt.trichotomy (a b : ℕ) : a < b ⊎ a = b ⊎ b < a :=
  begin
    revert b, induction a with a IH,
    { intro b, cases b,
        exact inr (inl idp),
        exact inl !zero_lt_succ},
    { intro b, cases b with b,
        exact inr (inr !zero_lt_succ),
      { cases IH b with H H,
          exact inl (succ_le_succ H),
          cases H with H H,
            exact inr (inl (ap succ H)),
            exact inr (inr (succ_le_succ H))}}
  end

  definition lt.by_cases {a b : ℕ} {P : Type} (H1 : a < b → P) (H2 : a = b → P) (H3 : b < a → P) : P :=
  by induction (lt.trichotomy a b) with H H; exact H1 H; cases H with H H; exact H2 H;exact H3 H

  definition lt_ge_by_cases {a b : ℕ} {P : Type} (H1 : a < b → P) (H2 : a ≥ b → P) : P :=
  lt.by_cases H1 (λH, H2 (le_of_eq H⁻¹)) (λH, H2 (le_of_lt H))

  definition lt_or_ge (a b : ℕ) : (a < b) ⊎ (a ≥ b) :=
  lt_ge_by_cases inl inr

  definition not_lt_zero (a : ℕ) : ¬ a < zero :=
  by intro H; cases H

  -- less-than is well-founded
  definition lt.wf [instance] : well_founded lt :=
  begin
    constructor, intro n, induction n with n IH,
    { constructor, intros n H, exfalso, exact !not_lt_zero H},
    { constructor, intros m H,
      assert aux : ∀ {n₁} (hlt : m < n₁), succ n = n₁ → acc lt m,
        { intros n₁ hlt, induction hlt,
          { intro p, injection p with q, exact q ▸ IH},
          { intro p, injection p with q, exact (acc.inv (q ▸ IH) a)}},
      apply aux H idp},
  end

  definition measure {A : Type} (f : A → ℕ) : A → A → Type₀ :=
  inv_image lt f

  definition measure.wf {A : Type} (f : A → ℕ) : well_founded (measure f) :=
  inv_image.wf f lt.wf

  definition succ_lt_succ {a b : ℕ} (H : a < b) : succ a < succ b :=
  succ_le_succ H

  definition lt_of_succ_lt {a b : ℕ} (H : succ a < b) : a < b :=
  le_of_succ_le H

  definition lt_of_succ_lt_succ {a b : ℕ} (H : succ a < succ b) : a < b :=
  le_of_succ_le_succ H

  definition decidable_le [instance] : decidable_rel le :=
  begin
    intros n, induction n with n IH,
    { intro m, left, apply zero_le},
    { intro m, cases m with m,
      { right, apply not_succ_le_zero},
      { let H := IH m, clear IH,
        cases H with H H,
          left, exact succ_le_succ H,
          right, intro H2, exact H (le_of_succ_le_succ H2)}}
  end

  definition decidable_lt [instance] : decidable_rel lt := _
  definition decidable_gt [instance] : decidable_rel gt := _
  definition decidable_ge [instance] : decidable_rel ge := _

  definition eq_or_lt_of_le {a b : ℕ} (H : a ≤ b) : a = b ⊎ a < b :=
  by cases H with b' H; exact sum.inl rfl; exact sum.inr (succ_le_succ H)


  definition le_of_eq_or_lt {a b : ℕ} (H : a = b ⊎ a < b) : a ≤ b :=
  by cases H with H H; exact le_of_eq H; exact le_of_lt H

  definition eq_or_lt_of_not_lt {a b : ℕ} (hnlt : ¬ a < b) : a = b ⊎ b < a :=
  sum.rec_on (lt.trichotomy a b)
    (λ hlt, absurd hlt hnlt)
    (λ h, h)

  definition lt_succ_of_le {a b : ℕ} (h : a ≤ b) : a < succ b :=
  succ_le_succ h

  definition lt_of_succ_le {a b : ℕ} (h : succ a ≤ b) : a < b := h

  definition succ_le_of_lt {a b : ℕ} (h : a < b) : succ a ≤ b := h

  definition max (a b : ℕ) : ℕ := if a < b then b else a
  definition min (a b : ℕ) : ℕ := if a < b then a else b

  definition max_self (a : ℕ) : max a a = a :=
  eq.rec_on !if_t_t rfl

  definition max_eq_right {a b : ℕ} (H : a < b) : max a b = b :=
  if_pos H

  definition max_eq_left {a b : ℕ} (H : ¬ a < b) : max a b = a :=
  if_neg H

  definition eq_max_right {a b : ℕ} (H : a < b) : b = max a b :=
  eq.rec_on (max_eq_right H) rfl

  definition eq_max_left {a b : ℕ} (H : ¬ a < b) : a = max a b :=
  eq.rec_on (max_eq_left H) rfl

  definition le_max_left (a b : ℕ) : a ≤ max a b :=
  by_cases
    (λ h : a < b,   le_of_lt (eq.rec_on (eq_max_right h) h))
    (λ h : ¬ a < b, eq.rec_on (eq_max_left h) !le.refl)

  definition le_max_right (a b : ℕ) : b ≤ max a b :=
  by_cases
    (λ h : a < b,   eq.rec_on (eq_max_right h) !le.refl)
    (λ h : ¬ a < b, sum.rec_on (eq_or_lt_of_not_lt h)
      (λ heq, eq.rec_on heq (eq.rec_on (inverse (max_self a)) !le.refl))
      (λ h : b < a,
        have aux : a = max a b, from eq_max_left (lt.asymm h),
        eq.rec_on aux (le_of_lt h)))

  definition succ_sub_succ_eq_sub (a b : ℕ) : succ a - succ b = a - b :=
  by induction b with b IH; reflexivity; apply ap pred IH

  definition sub_eq_succ_sub_succ (a b : ℕ) : a - b = succ a - succ b :=
  eq.rec_on (succ_sub_succ_eq_sub a b) rfl

  definition zero_sub_eq_zero (a : ℕ) : zero - a = zero :=
  nat.rec_on a
    rfl
    (λ a₁ (ih : zero - a₁ = zero), ap pred ih)

  definition zero_eq_zero_sub (a : ℕ) : zero = zero - a :=
  eq.rec_on (zero_sub_eq_zero a) rfl

  definition sub_lt {a b : ℕ} : zero < a → zero < b → a - b < a :=
  have aux : Π {a}, zero < a → Π {b}, zero < b → a - b < a, from
    λa h₁, le.rec_on h₁
      (λb h₂, le.cases_on h₂
        (lt.base zero)
        (λ b₁ bpos,
          eq.rec_on (sub_eq_succ_sub_succ zero b₁)
           (eq.rec_on (zero_eq_zero_sub b₁) (lt.base zero))))
      (λa₁ apos ih b h₂, le.cases_on h₂
        (lt.base a₁)
        (λ b₁ bpos,
          eq.rec_on (sub_eq_succ_sub_succ a₁ b₁)
            (lt.trans (@ih b₁ bpos) (lt.base a₁)))),
  λ h₁ h₂, aux h₁ h₂

  definition sub_le (a b : ℕ) : a - b ≤ a :=
  nat.rec_on b
    (le.refl a)
    (λ b₁ ih, le.trans !pred_le ih)

  lemma sub_lt_succ (a b : ℕ) : a - b < succ a := lt_succ_of_le (sub_le a b)
end nat
