/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.nat init.meta

namespace nat

  protected lemma zero_add : ∀ n : ℕ, 0 + n = n
  | 0     := rfl
  | (n+1) := congr_arg succ (zero_add n)

  lemma succ_add : ∀ n m : ℕ, (succ n) + m = succ (n + m)
  | n 0     := rfl
  | n (m+1) := congr_arg succ (succ_add n m)

  protected lemma add_comm : ∀ n m : ℕ, n + m = m + n
  | n 0     := eq.symm (nat.zero_add n)
  | n (m+1) :=
    suffices succ (n + m) = succ (m + n), from
      eq.symm (succ_add m n) ▸ this,
    congr_arg succ (add_comm n m)

  protected lemma bit0_succ_eq (n : ℕ) : bit0 (succ n) = succ (succ (bit0 n)) :=
  show succ (succ n + n) = succ (succ (n + n)), from
  congr_arg succ (succ_add n n)

  protected lemma bit1_eq_succ_bit0 (n : ℕ) : bit1 n = succ (bit0 n) :=
  rfl

  protected lemma bit1_succ_eq (n : ℕ) : bit1 (succ n) = succ (succ (bit1 n)) :=
  eq.trans (nat.bit1_eq_succ_bit0 (succ n)) (congr_arg succ (nat.bit0_succ_eq n))

  lemma succ_ne_zero (n : ℕ) : succ n ≠ 0 :=
  assume h, nat.no_confusion h

  lemma succ_ne_self : ∀ n : ℕ, succ n ≠ n
  | 0     h := absurd h (nat.succ_ne_zero 0)
  | (n+1) h := succ_ne_self n (nat.no_confusion h (λ h, h))

  protected lemma one_ne_zero : 1 ≠ (0 : ℕ) :=
  assume h, nat.no_confusion h

  protected lemma bit0_ne_zero : ∀ n : ℕ, n ≠ 0 → bit0 n ≠ 0
  | 0     h := absurd rfl h
  | (n+1) h := nat.succ_ne_zero _

  protected lemma bit1_ne_zero (n : ℕ) : bit1 n ≠ 0 :=
  show succ (n + n) ≠ 0, from
  succ_ne_zero (n + n)

  protected lemma bit1_ne_one : ∀ n : ℕ, n ≠ 0 → bit1 n ≠ 1
  | 0     h h1 := absurd rfl h
  | (n+1) h h1 := nat.no_confusion h1 (λ h2, absurd h2 (nat.succ_ne_zero _))

  protected lemma bit0_ne_one : ∀ n : ℕ, bit0 n ≠ 1
  | 0     h := absurd h (ne.symm nat.one_ne_zero)
  | (n+1) h :=
    have h1 : succ (succ (n + n)) = 1, from succ_add n n ▸ h,
    nat.no_confusion h1
      (λ h2, absurd h2 (succ_ne_zero (n + n)))

  protected lemma add_self_ne_one : ∀ (n : ℕ), n + n ≠ 1
  | 0     h := nat.no_confusion h
  | (n+1) h :=
    have h1 : succ (succ (n + n)) = 1, from succ_add n n ▸ h,
    nat.no_confusion h1 (λ h2, absurd h2 (nat.succ_ne_zero (n + n)))

  protected lemma bit1_ne_bit0 : ∀ (n m : ℕ), bit1 n ≠ bit0 m
  | 0     m     h := absurd h (ne.symm (nat.add_self_ne_one m))
  | (n+1) 0     h :=
    have h1 : succ (bit0 (succ n)) = 0, from h,
    absurd h1 (nat.succ_ne_zero _)
  | (n+1) (m+1) h :=
    have h1 : succ (succ (bit1 n)) = succ (succ (bit0 m)), from
      nat.bit0_succ_eq m ▸ nat.bit1_succ_eq n ▸ h,
    have h2 : bit1 n = bit0 m, from
      nat.no_confusion h1 (λ h2', nat.no_confusion h2' (λ h2'', h2'')),
    absurd h2 (bit1_ne_bit0 n m)

  /- properties of inequality -/

  protected lemma le_of_eq {n m : ℕ} (p : n = m) : n ≤ m :=
  p ▸ le.nat_refl n

  @[simp] lemma le_succ_iff_true (n : ℕ) : n ≤ succ n ↔ true :=
  iff_true_intro (le_succ n)

  @[simp] lemma pred_le_iff_true (n : ℕ) : pred n ≤ n ↔ true :=
  iff_true_intro (pred_le n)


  lemma le_succ_of_le {n m : ℕ} (h : n ≤ m) : n ≤ succ m :=
  nat.le_trans h (le_succ m)

  lemma le_of_succ_le {n m : ℕ} (h : succ n ≤ m) : n ≤ m :=
  nat.le_trans (le_succ n) h

  protected lemma le_of_lt {n m : ℕ} (h : n < m) : n ≤ m :=
  le_of_succ_le h


  lemma le_succ_of_pred_le {n m : ℕ} : pred n ≤ m → n ≤ succ m :=
  nat.cases_on n le.step (λ a, succ_le_succ)

  lemma succ_le_zero_iff_false (n : ℕ) : succ n ≤ 0 ↔ false :=
  iff_false_intro (not_succ_le_zero n)


  @[simp] lemma succ_le_self_iff_false (n : ℕ) : succ n ≤ n ↔ false :=
  iff_false_intro (not_succ_le_self n)

  @[simp] lemma zero_le_iff_true (n : ℕ) : 0 ≤ n ↔ true :=
  iff_true_intro (zero_le n)

  protected lemma one_le_bit1 (n : ℕ) : 1 ≤ bit1 n :=
  show 1 ≤ succ (bit0 n), from
  succ_le_succ (zero_le (bit0 n))

  protected lemma one_le_bit0 : ∀ (n : ℕ), n ≠ 0 → 1 ≤ bit0 n
  | 0     h := absurd rfl h
  | (n+1) h :=
    suffices 1 ≤ succ (succ (bit0 n)), from
      eq.symm (nat.bit0_succ_eq n) ▸ this,
    succ_le_succ (zero_le (succ (bit0 n)))

  def lt.step {n m : ℕ} : n < m → n < succ m := le.step

  @[simp] lemma zero_lt_succ_iff_true (n : ℕ) : 0 < succ n ↔ true :=
  iff_true_intro (zero_lt_succ n)

  protected lemma lt_trans {n m k : ℕ} (h₁ : n < m) : m < k → n < k :=
  nat.le_trans (le.step h₁)

  protected lemma lt_of_le_of_lt {n m k : ℕ} (h₁ : n ≤ m) : m < k → n < k :=
  nat.le_trans (succ_le_succ h₁)

  lemma lt_self_iff_false (n : ℕ) : n < n ↔ false :=
  iff_false_intro (λ h, absurd h (nat.lt_irrefl n))

  lemma self_lt_succ (n : ℕ) : n < succ n := nat.le_refl (succ n)

  @[simp] lemma self_lt_succ_iff_true (n : ℕ) : n < succ n ↔ true :=
  iff_true_intro (self_lt_succ n)

  def lt.base (n : ℕ) : n < succ n := nat.le_refl (succ n)

  lemma le_lt_antisymm {n m : ℕ} (h₁ : n ≤ m) (h₂ : m < n) : false :=
  nat.lt_irrefl n (nat.lt_of_le_of_lt h₁ h₂)

  protected lemma le_antisymm {n m : ℕ} (h₁ : n ≤ m) : m ≤ n → n = m :=
  le.cases_on h₁ (λ a, rfl) (λ a b c, absurd (nat.lt_of_le_of_lt b c) (nat.lt_irrefl n))

  instance : weak_order ℕ :=
    ⟨ @nat.le, @nat.le_refl, @nat.le_trans, @nat.le_antisymm ⟩

  lemma lt_le_antisymm {n m : ℕ} (h₁ : n < m) (h₂ : m ≤ n) : false :=
  le_lt_antisymm h₂ h₁

  protected lemma nat.lt_asymm {n m : ℕ} (h₁ : n < m) : ¬ m < n :=
  le_lt_antisymm (nat.le_of_lt h₁)

  attribute [simp]
  lemma lt_zero_iff_false (a : ℕ) : a < 0 ↔ false :=
  iff_false_intro (not_lt_zero a)

  protected lemma le_of_eq_or_lt {a b : ℕ} (h : a = b ∨ a < b) : a ≤ b :=
  or.elim h nat.le_of_eq nat.le_of_lt

  lemma succ_lt_succ {a b : ℕ} : a < b → succ a < succ b :=
  succ_le_succ

  lemma lt_of_succ_lt {a b : ℕ} : succ a < b → a < b :=
  le_of_succ_le

  lemma lt_of_succ_lt_succ {a b : ℕ} : succ a < succ b → a < b :=
  le_of_succ_le_succ


  protected lemma lt_or_ge : ∀ (a b : ℕ), a < b ∨ a ≥ b
  | a 0     := or.inr (zero_le a)
  | a (b+1) :=
    match lt_or_ge a b with
    | or.inl h := or.inl (le_succ_of_le h)
    | or.inr h :=
      match nat.eq_or_lt_of_le h with
      | or.inl h1 := or.inl (h1 ▸ self_lt_succ b)
      | or.inr h1 := or.inr h1
      end
    end

  protected def {u} lt_ge_by_cases {a b : ℕ} {C : Type u} (h₁ : a < b → C) (h₂ : a ≥ b → C) : C :=
  decidable.by_cases h₁ (λ h, h₂ (or.elim (nat.lt_or_ge a b) (λ a, absurd a h) (λ a, a)))

  protected def {u} lt_by_cases {a b : ℕ} {C : Type u} (h₁ : a < b → C) (h₂ : a = b → C)
    (h₃ : b < a → C) : C :=
  nat.lt_ge_by_cases h₁ (λ h₁,
    nat.lt_ge_by_cases h₃ (λ h, h₂ (nat.le_antisymm h h₁)))

  protected lemma lt_trichotomy (a b : ℕ) : a < b ∨ a = b ∨ b < a :=
  nat.lt_by_cases (λ h, or.inl h) (λ h, or.inr (or.inl h)) (λ h, or.inr (or.inr h))

  protected lemma eq_or_lt_of_not_lt {a b : ℕ} (hnlt : ¬ a < b) : a = b ∨ b < a :=
  or.elim (nat.lt_trichotomy a b)
    (λ hlt, absurd hlt hnlt)
    (λ h, h)


  lemma lt_of_succ_le {a b : ℕ} (h : succ a ≤ b) : a < b := h

  lemma succ_le_of_lt {a b : ℕ} (h : a < b) : succ a ≤ b := h


  lemma sub_eq_succ_sub_succ (a b : ℕ) : a - b = succ a - succ b :=
  eq.symm (succ_sub_succ_eq_sub a b)

  @[simp] lemma zero_sub_eq_zero : ∀ a : ℕ, 0 - a = 0
  | 0     := rfl
  | (a+1) := congr_arg pred (zero_sub_eq_zero a)

  lemma zero_eq_zero_sub (a : ℕ) : 0 = 0 - a :=
  eq.symm (zero_sub_eq_zero a)


  @[simp] lemma sub_le_iff_true (a b : ℕ) : a - b ≤ a ↔ true :=
  iff_true_intro (sub_le a b)

  lemma sub_lt_succ (a b : ℕ) : a - b < succ a :=
  lt_succ_of_le (sub_le a b)

  @[simp] lemma sub_lt_succ_iff_true (a b : ℕ) : a - b < succ a ↔ true :=
  iff_true_intro (sub_lt_succ a b)

  lemma le_add_right : ∀ (n k : ℕ), n ≤ n + k
  | n 0     := nat.le_refl n
  | n (k+1) := le_succ_of_le (le_add_right n k)

  lemma le_add_left (n m : ℕ): n ≤ m + n :=
  nat.add_comm n m ▸ le_add_right n m

end nat
