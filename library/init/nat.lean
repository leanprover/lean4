/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura
-/
prelude
import init.relation init.num
open decidable or

notation `ℕ` := nat

namespace nat
  attribute [reducible]
  protected definition rec_on
                       {C : ℕ → Type} (n : ℕ) (H₁ : C 0) (H₂ : Π (a : ℕ), C a → C (succ a)) : C n :=
  nat.rec H₁ H₂ n

  protected theorem induction_on
                       {C : ℕ → Prop} (n : ℕ) (H₁ : C 0) (H₂ : Π (a : ℕ), C a → C (succ a)) : C n :=
  nat.rec H₁ H₂ n

  attribute [reducible]
  protected definition cases_on
                       {C : ℕ → Type} (n : ℕ) (H₁ : C 0) (H₂ : Π (a : ℕ), C (succ a)) : C n :=
  nat.rec H₁ (λ a ih, H₂ a) n

  attribute nat.rec_on [recursor] -- Hack: force rec_on to be the first one. TODO(Leo): we should add priorities to recursors

  attribute [reducible]
  protected definition no_confusion_type (P : Type) (v₁ v₂ : ℕ) : Type :=
  nat.rec
    (nat.rec (P → P) (λ a₂ ih, P) v₂)
    (λ a₁ ih, nat.rec P (λ a₂ ih, (a₁ = a₂ → P) → P) v₂)
    v₁

  attribute [reducible, unfold 4]
  protected definition no_confusion
                       {P : Type} {v₁ v₂ : ℕ} (H : v₁ = v₂) : nat.no_confusion_type P v₁ v₂ :=
  have v₁ = v₁ → nat.no_confusion_type P v₁ v₁, from
    λ H₁ : v₁ = v₁, nat.rec (λ h, h) (λ a ih h, h (eq.refl a)) v₁,
  have v₁ = v₂ → nat.no_confusion_type P v₁ v₂, from
    eq.rec this H,
  this H

  /- basic definitions on natural numbers -/
  inductive le (a : ℕ) : ℕ → Prop :=
  | nat_refl : le a a    -- use nat_refl to avoid overloading le.refl
  | step : Π {b}, le a b → le a (succ b)

  definition nat_has_le : has_le nat := has_le.mk nat.le

  local attribute [instance, priority nat.prio] nat_has_le

  attribute [refl]
  protected lemma le_refl : ∀ a : nat, a ≤ a :=
  le.nat_refl

  attribute [reducible]
  protected definition lt (n m : ℕ) := succ n ≤ m
  definition nat_has_lt : has_lt nat := has_lt.mk nat.lt

  attribute [unfold 1]
  definition pred (a : nat) : nat :=
  nat.cases_on a zero (λ a₁, a₁)

  -- add is defined in init.reserved_notation

  protected definition sub (a b : nat) : nat :=
  nat.rec_on b a (λ b₁, pred)

  protected definition mul (a b : nat) : nat :=
  nat.rec_on b zero (λ b₁ r, r + a)

  definition nat_has_sub : has_sub nat :=
  has_sub.mk nat.sub

  definition nat_has_mul : has_mul nat :=
  has_mul.mk nat.mul

  local attribute [instance, priority nat.prio] nat_has_sub nat_has_mul nat_has_lt

  /- properties of ℕ -/

  protected definition has_decidable_eq : ∀ x y : nat, decidable (x = y)
  | has_decidable_eq zero     zero     := tt rfl
  | has_decidable_eq (succ x) zero     := ff (λ H, nat.no_confusion H)
  | has_decidable_eq zero     (succ y) := ff (λ H, nat.no_confusion H)
  | has_decidable_eq (succ x) (succ y) :=
      match (has_decidable_eq x y) with
      | (tt xeqy) := tt (eq.subst xeqy (eq.refl (succ x)))
      | (ff xney) := ff (λ H : succ x = succ y, nat.no_confusion H (λ xeqy : x = y, absurd xeqy xney))
      end

  local attribute [instance, priority nat.prio] nat.has_decidable_eq

  /- properties of inequality -/

  protected theorem le_of_eq {n m : ℕ} (p : n = m) : n ≤ m :=
  eq.subst p (le.nat_refl n)

  theorem le_succ (n : ℕ) : n ≤ succ n :=
  le.step (nat.le_refl n)

  theorem pred_le : ∀ (n : ℕ), pred n ≤ n
  | 0        := le.nat_refl 0
  | (succ a) := le.step (le.nat_refl a)

  attribute [simp]
  theorem le_succ_iff_true (n : ℕ) : n ≤ succ n ↔ true :=
  iff_true_intro (le_succ n)

  attribute [simp]
  theorem pred_le_iff_true (n : ℕ) : pred n ≤ n ↔ true :=
  iff_true_intro (pred_le n)

  protected theorem le_trans {n m k : ℕ} (H1 : n ≤ m) : m ≤ k → n ≤ k :=
  le.rec H1 (λp H2, le.step)

  theorem le_succ_of_le {n m : ℕ} (H : n ≤ m) : n ≤ succ m :=
  nat.le_trans H (le_succ m)

  theorem le_of_succ_le {n m : ℕ} (H : succ n ≤ m) : n ≤ m :=
  nat.le_trans (le_succ n) H

  protected theorem le_of_lt {n m : ℕ} (H : n < m) : n ≤ m :=
  le_of_succ_le H

  theorem succ_le_succ {n m : ℕ} : n ≤ m → succ n ≤ succ m :=
  le.rec (nat.le_refl (succ n)) (λa b, le.step)

  theorem pred_le_pred {n m : ℕ} : n ≤ m → pred n ≤ pred m :=
  le.rec (nat.le_refl (pred n)) (nat.rec (λa b, b) (λa b c, le.step))

  theorem le_of_succ_le_succ {n m : ℕ} : succ n ≤ succ m → n ≤ m :=
  pred_le_pred

  theorem le_succ_of_pred_le {n m : ℕ} : pred n ≤ m → n ≤ succ m :=
  nat.cases_on n le.step (λa, succ_le_succ)

  theorem not_succ_le_zero (n : ℕ) : ¬succ n ≤ 0 :=
  assume H : succ n ≤ 0,
  have 0 = 0 → false, from
    (le.cases_on H
       (λ H1 : 0 = succ n, nat.no_confusion H1)
       (λ (b : ℕ) (a : succ n ≤ b) (H1 : 0 = succ b), nat.no_confusion H1)),
  this rfl

  theorem succ_le_zero_iff_false (n : ℕ) : succ n ≤ 0 ↔ false :=
  iff_false_intro (not_succ_le_zero n)

  theorem not_succ_le_self : Π {n : ℕ}, ¬succ n ≤ n :=
  nat.rec (not_succ_le_zero 0) (λa b c, b (le_of_succ_le_succ c))

  attribute [simp]
  theorem succ_le_self_iff_false (n : ℕ) : succ n ≤ n ↔ false :=
  iff_false_intro not_succ_le_self

  theorem zero_le : ∀ (n : ℕ), 0 ≤ n :=
  nat.rec (nat.le_refl 0) (λa, le.step)

  attribute [simp]
  theorem zero_le_iff_true (n : ℕ) : 0 ≤ n ↔ true :=
  iff_true_intro (zero_le n)

  theorem lt.step {n m : ℕ} : n < m → n < succ m := le.step

  theorem zero_lt_succ (n : ℕ) : 0 < succ n :=
  succ_le_succ (zero_le n)

  attribute [simp]
  theorem zero_lt_succ_iff_true (n : ℕ) : 0 < succ n ↔ true :=
  iff_true_intro (zero_lt_succ n)

  protected theorem lt_trans {n m k : ℕ} (H1 : n < m) : m < k → n < k :=
  nat.le_trans (le.step H1)

  protected theorem lt_of_le_of_lt {n m k : ℕ} (H1 : n ≤ m) : m < k → n < k :=
  nat.le_trans (succ_le_succ H1)

  protected theorem lt_of_lt_of_le {n m k : ℕ} : n < m → m ≤ k → n < k := nat.le_trans

  protected theorem lt_irrefl (n : ℕ) : ¬n < n := not_succ_le_self

  theorem lt_self_iff_false (n : ℕ) : n < n ↔ false :=
  iff_false_intro (λ H, absurd H (nat.lt_irrefl n))

  theorem self_lt_succ (n : ℕ) : n < succ n := nat.le_refl (succ n)

  attribute [simp]
  theorem self_lt_succ_iff_true (n : ℕ) : n < succ n ↔ true :=
  iff_true_intro (self_lt_succ n)

  theorem lt.base (n : ℕ) : n < succ n := nat.le_refl (succ n)

  theorem le_lt_antisymm {n m : ℕ} (H1 : n ≤ m) (H2 : m < n) : false :=
  nat.lt_irrefl n (nat.lt_of_le_of_lt H1 H2)

  protected theorem le_antisymm {n m : ℕ} (H1 : n ≤ m) : m ≤ n → n = m :=
  le.cases_on H1 (λa, rfl) (λa b c, absurd (nat.lt_of_le_of_lt b c) (nat.lt_irrefl n))

  theorem lt_le_antisymm {n m : ℕ} (H1 : n < m) (H2 : m ≤ n) : false :=
  le_lt_antisymm H2 H1

  protected theorem nat.lt_asymm {n m : ℕ} (H1 : n < m) : ¬ m < n :=
  le_lt_antisymm (nat.le_of_lt H1)

  theorem not_lt_zero (a : ℕ) : ¬ a < 0 := not_succ_le_zero a

  attribute [simp]
  theorem lt_zero_iff_false (a : ℕ) : a < 0 ↔ false :=
  iff_false_intro (not_lt_zero a)

  protected theorem eq_or_lt_of_le {a b : ℕ} (H : a ≤ b) : a = b ∨ a < b :=
  le.cases_on H (inl rfl) (λn h, inr (succ_le_succ h))

  protected theorem le_of_eq_or_lt {a b : ℕ} (H : a = b ∨ a < b) : a ≤ b :=
  or.elim H nat.le_of_eq nat.le_of_lt

  theorem succ_lt_succ {a b : ℕ} : a < b → succ a < succ b :=
  succ_le_succ

  theorem lt_of_succ_lt {a b : ℕ} : succ a < b → a < b :=
  le_of_succ_le

  theorem lt_of_succ_lt_succ {a b : ℕ} : succ a < succ b → a < b :=
  le_of_succ_le_succ

  protected definition decidable_le : ∀ a b : nat, decidable (a ≤ b)  :=
  nat.rec (λm, (decidable.tt (zero_le m)))
     (λn IH m, nat.cases_on m
       (decidable.ff (not_succ_le_zero n))
       (λm, decidable.rec_on (IH m)
          (λH, decidable.ff (λa, H (le_of_succ_le_succ a)))
          (λH, decidable.tt (succ_le_succ H))))

  protected definition decidable_lt : ∀ a b : nat, decidable (a < b) :=
  λ a b, nat.decidable_le (succ a) b

  local attribute [instance, priority nat.prio] nat.has_decidable_eq nat.decidable_le nat.decidable_lt

  protected theorem lt_or_ge (a b : ℕ) : a < b ∨ a ≥ b :=
  nat.rec_on b (inr (zero_le a)) (λn, or.rec
    (λh, inl (le_succ_of_le h))
    (λh, or.elim (nat.eq_or_lt_of_le h)
         (λe : n = a, inl ((eq.subst e (λ (h : n ≤ n), iff.mpr (self_lt_succ_iff_true n) true.intro)) h))
         inr))

  protected definition lt_ge_by_cases {a b : ℕ} {P : Type} (H1 : a < b → P) (H2 : a ≥ b → P) : P :=
  by_cases H1 (λh, H2 (or.elim (nat.lt_or_ge a b) (λa, absurd a h) (λa, a)))

  protected definition lt_by_cases {a b : ℕ} {P : Type} (H1 : a < b → P) (H2 : a = b → P)
    (H3 : b < a → P) : P :=
  nat.lt_ge_by_cases H1 (λh₁,
    nat.lt_ge_by_cases H3 (λh₂, H2 (nat.le_antisymm h₂ h₁)))

  protected theorem lt_trichotomy (a b : ℕ) : a < b ∨ a = b ∨ b < a :=
  nat.lt_by_cases (λH, inl H) (λH, inr (inl H)) (λH, inr (inr H))

  protected theorem eq_or_lt_of_not_lt {a b : ℕ} (hnlt : ¬ a < b) : a = b ∨ b < a :=
  or.rec_on (nat.lt_trichotomy a b)
    (λ hlt, absurd hlt hnlt)
    (λ h, h)

  theorem lt_succ_of_le {a b : ℕ} : a ≤ b → a < succ b :=
  succ_le_succ

  theorem lt_of_succ_le {a b : ℕ} (h : succ a ≤ b) : a < b := h

  theorem succ_le_of_lt {a b : ℕ} (h : a < b) : succ a ≤ b := h

  attribute [simp]
  theorem succ_sub_succ_eq_sub (a b : ℕ) : succ a - succ b = a - b :=
  nat.rec_on b
    (show succ a - succ zero = a - zero, from (eq.refl (succ a - succ zero)))
    (λ b, congr_arg pred)

  theorem sub_eq_succ_sub_succ (a b : ℕ) : a - b = succ a - succ b :=
  eq.symm (succ_sub_succ_eq_sub a b)

  attribute [simp]
  theorem zero_sub_eq_zero (a : ℕ) : 0 - a = 0 :=
  nat.rec rfl (λ a, congr_arg pred) a

  theorem zero_eq_zero_sub (a : ℕ) : 0 = 0 - a :=
  eq.symm (zero_sub_eq_zero a)

  theorem sub_le (a b : ℕ) : a - b ≤ a :=
  nat.rec_on b (nat.le_refl (a - 0)) (λ b₁, nat.le_trans (pred_le (a - b₁)))

  attribute [simp]
  theorem sub_le_iff_true (a b : ℕ) : a - b ≤ a ↔ true :=
  iff_true_intro (sub_le a b)

  theorem sub_lt {a b : ℕ} (H1 : 0 < a) (H2 : 0 < b) : a - b < a :=
  nat.cases_on a
    (λh, absurd h (nat.lt_irrefl 0))
    (λa h, succ_le_succ (nat.cases_on b
      (λh, absurd h (nat.lt_irrefl 0))
      (λb c, eq.substr (succ_sub_succ_eq_sub a b) (sub_le a b)) H2)) H1

  theorem sub_lt_succ (a b : ℕ) : a - b < succ a :=
  lt_succ_of_le (sub_le a b)

  attribute [simp]
  theorem sub_lt_succ_iff_true (a b : ℕ) : a - b < succ a ↔ true :=
  iff_true_intro (sub_lt_succ a b)

  definition repeat {A : Type} (f : nat → A → A) : nat → A → A
  | 0         a := a
  | (succ n)  a := f n (repeat n a)

end nat

attribute [instance]
protected definition nat.is_inhabited : inhabited nat :=
inhabited.mk nat.zero

attribute [recursor] nat.induction_on
attribute [recursor, unfold 2] nat.cases_on
attribute [recursor, unfold 2] nat.rec_on
attribute [instance, priority nat.prio]
   nat.nat_has_le nat.nat_has_sub nat.nat_has_mul nat.nat_has_lt
   nat.has_decidable_eq nat.decidable_le nat.decidable_lt
