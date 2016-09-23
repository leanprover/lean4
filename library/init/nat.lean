/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura
-/
prelude
import init.relation init.num

notation `ℕ` := nat

namespace nat
  protected theorem zero_add : ∀ n : ℕ, 0 + n = n
  | 0     := rfl
  | (n+1) := congr_arg succ (zero_add n)

  theorem succ_add : ∀ n m : ℕ, (succ n) + m = succ (n + m)
  | n 0     := rfl
  | n (m+1) := congr_arg succ (succ_add n m)

  protected theorem add_comm : ∀ n m : ℕ, n + m = m + n
  | n 0     := eq.symm (nat.zero_add n)
  | n (m+1) :=
    suffices succ (n + m) = succ (m + n), from
      eq.symm (succ_add m n) ▸ this,
    congr_arg succ (add_comm n m)

  protected theorem bit0_succ_eq (n : ℕ) : bit0 (succ n) = succ (succ (bit0 n)) :=
  show succ (succ n + n) = succ (succ (n + n)), from
  succ_add n n ▸ rfl

  protected theorem bit1_eq_succ_bit0 (n : ℕ) : bit1 n = succ (bit0 n) :=
  rfl

  protected theorem bit1_succ_eq (n : ℕ) : bit1 (succ n) = succ (succ (bit1 n)) :=
  eq.trans (nat.bit1_eq_succ_bit0 (succ n)) (congr_arg succ (nat.bit0_succ_eq n))

  theorem succ_ne_zero (n : ℕ) : succ n ≠ 0 :=
  assume h, nat.no_confusion h

  theorem succ_ne_self : ∀ n : ℕ, succ n ≠ n
  | 0     h := absurd h (nat.succ_ne_zero 0)
  | (n+1) h := succ_ne_self n (nat.no_confusion h (λ h, h))

  protected theorem one_ne_zero : 1 ≠ (0 : ℕ) :=
  assume h, nat.no_confusion h

  protected theorem bit0_ne_zero : ∀ n : ℕ, n ≠ 0 → bit0 n ≠ 0
  | 0     h := absurd rfl h
  | (n+1) h := nat.succ_ne_zero _

  protected theorem bit1_ne_zero (n : ℕ) : bit1 n ≠ 0 :=
  show succ (n + n) ≠ 0, from
  succ_ne_zero (n + n)

  protected theorem bit1_ne_one : ∀ n : ℕ, n ≠ 0 → bit1 n ≠ 1
  | 0     h h1 := absurd rfl h
  | (n+1) h h1 := nat.no_confusion h1 (λ h2, absurd h2 (nat.succ_ne_zero _))

  protected theorem bit0_ne_one : ∀ n : ℕ, bit0 n ≠ 1
  | 0     h := absurd h (ne.symm nat.one_ne_zero)
  | (n+1) h :=
    have h1 : succ (succ (n + n)) = 1, from succ_add n n ▸ h,
    nat.no_confusion h1
      (λ h2, absurd h2 (succ_ne_zero (n + n)))

  protected theorem add_self_ne_one : ∀ (n : ℕ), n + n ≠ 1
  | 0     h := nat.no_confusion h
  | (n+1) h :=
    have h1 : succ (succ (n + n)) = 1, from succ_add n n ▸ h,
    nat.no_confusion h1 (λ h2, absurd h2 (nat.succ_ne_zero (n + n)))

  protected theorem bit1_ne_bit0 : ∀ (n m : ℕ), bit1 n ≠ bit0 m
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

  inductive le (a : ℕ) : ℕ → Prop
  | nat_refl : le a    -- use nat_refl to avoid overloading le.refl
  | step : Π {b}, le b → le (succ b)

  instance : has_le ℕ :=
  ⟨nat.le⟩

  attribute [refl]
  protected definition le_refl : ∀ a : ℕ, a ≤ a :=
  le.nat_refl

  attribute [reducible]
  protected definition lt (n m : ℕ) := succ n ≤ m

  instance : has_lt ℕ :=
  ⟨nat.lt⟩

  definition pred : ℕ → ℕ
  | 0     := 0
  | (a+1) := a

  protected definition sub : ℕ → ℕ → ℕ
  | a 0     := a
  | a (b+1) := pred (sub a b)

  protected definition mul (a b : ℕ) : ℕ :=
  nat.rec_on b zero (λ b₁ r, r + a)

  instance : has_sub ℕ :=
  ⟨nat.sub⟩

  instance : has_mul ℕ :=
  ⟨nat.mul⟩

  instance : decidable_eq ℕ
  | zero     zero     := is_true rfl
  | (succ x) zero     := is_false (λ h, nat.no_confusion h)
  | zero     (succ y) := is_false (λ h, nat.no_confusion h)
  | (succ x) (succ y) :=
      match decidable_eq x y with
      | is_true xeqy := is_true (xeqy ▸ eq.refl (succ x))
      | is_false xney := is_false (λ h, nat.no_confusion h (λ xeqy, absurd xeqy xney))
      end

  /- properties of inequality -/

  protected theorem le_of_eq {n m : ℕ} (p : n = m) : n ≤ m :=
  p ▸ le.nat_refl n

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

  protected theorem le_trans {n m k : ℕ} (h1 : n ≤ m) : m ≤ k → n ≤ k :=
  le.rec h1 (λ p h2, le.step)

  theorem le_succ_of_le {n m : ℕ} (h : n ≤ m) : n ≤ succ m :=
  nat.le_trans h (le_succ m)

  theorem le_of_succ_le {n m : ℕ} (h : succ n ≤ m) : n ≤ m :=
  nat.le_trans (le_succ n) h

  protected theorem le_of_lt {n m : ℕ} (h : n < m) : n ≤ m :=
  le_of_succ_le h

  theorem succ_le_succ {n m : ℕ} : n ≤ m → succ n ≤ succ m :=
  λ h, le.rec (nat.le_refl (succ n)) (λ a b, le.step) h

  theorem pred_le_pred {n m : ℕ} : n ≤ m → pred n ≤ pred m :=
  λ h, le.rec (nat.le_refl (pred n)) (λ n, nat.rec (λ a b, b) (λ a b c, le.step) n) h

  theorem le_of_succ_le_succ {n m : ℕ} : succ n ≤ succ m → n ≤ m :=
  pred_le_pred

  theorem le_succ_of_pred_le {n m : ℕ} : pred n ≤ m → n ≤ succ m :=
  nat.cases_on n le.step (λ a, succ_le_succ)

  theorem not_succ_le_zero : ∀ (n : ℕ), succ n ≤ 0 → false
  .

  theorem succ_le_zero_iff_false (n : ℕ) : succ n ≤ 0 ↔ false :=
  iff_false_intro (not_succ_le_zero n)

  theorem not_succ_le_self : ∀ n : ℕ, ¬succ n ≤ n :=
  λ n, nat.rec (not_succ_le_zero 0) (λ a b c, b (le_of_succ_le_succ c)) n

  attribute [simp]
  theorem succ_le_self_iff_false (n : ℕ) : succ n ≤ n ↔ false :=
  iff_false_intro (not_succ_le_self n)

  theorem zero_le : ∀ (n : ℕ), 0 ≤ n
  | 0     := nat.le_refl 0
  | (n+1) := le.step (zero_le n)

  attribute [simp]
  theorem zero_le_iff_true (n : ℕ) : 0 ≤ n ↔ true :=
  iff_true_intro (zero_le n)

  protected theorem one_le_bit1 (n : ℕ) : 1 ≤ bit1 n :=
  show 1 ≤ succ (bit0 n), from
  succ_le_succ (zero_le (bit0 n))

  protected theorem one_le_bit0 : ∀ (n : ℕ), n ≠ 0 → 1 ≤ bit0 n
  | 0     h := absurd rfl h
  | (n+1) h :=
    suffices 1 ≤ succ (succ (bit0 n)), from
      eq.symm (nat.bit0_succ_eq n) ▸ this,
    succ_le_succ (zero_le (succ (bit0 n)))

  definition lt.step {n m : ℕ} : n < m → n < succ m := le.step

  theorem zero_lt_succ (n : ℕ) : 0 < succ n :=
  succ_le_succ (zero_le n)

  attribute [simp]
  theorem zero_lt_succ_iff_true (n : ℕ) : 0 < succ n ↔ true :=
  iff_true_intro (zero_lt_succ n)

  protected theorem lt_trans {n m k : ℕ} (h₁ : n < m) : m < k → n < k :=
  nat.le_trans (le.step h₁)

  protected theorem lt_of_le_of_lt {n m k : ℕ} (h₁ : n ≤ m) : m < k → n < k :=
  nat.le_trans (succ_le_succ h₁)

  protected theorem lt_of_lt_of_le {n m k : ℕ} : n < m → m ≤ k → n < k := nat.le_trans

  protected theorem lt_irrefl (n : ℕ) : ¬n < n :=
  not_succ_le_self n

  theorem lt_self_iff_false (n : ℕ) : n < n ↔ false :=
  iff_false_intro (λ h, absurd h (nat.lt_irrefl n))

  theorem self_lt_succ (n : ℕ) : n < succ n := nat.le_refl (succ n)

  attribute [simp]
  theorem self_lt_succ_iff_true (n : ℕ) : n < succ n ↔ true :=
  iff_true_intro (self_lt_succ n)

  definition lt.base (n : ℕ) : n < succ n := nat.le_refl (succ n)

  theorem le_lt_antisymm {n m : ℕ} (h₁ : n ≤ m) (h₂ : m < n) : false :=
  nat.lt_irrefl n (nat.lt_of_le_of_lt h₁ h₂)

  protected theorem le_antisymm {n m : ℕ} (h₁ : n ≤ m) : m ≤ n → n = m :=
  le.cases_on h₁ (λ a, rfl) (λ a b c, absurd (nat.lt_of_le_of_lt b c) (nat.lt_irrefl n))

  theorem lt_le_antisymm {n m : ℕ} (h₁ : n < m) (h₂ : m ≤ n) : false :=
  le_lt_antisymm h₂ h₁

  protected theorem nat.lt_asymm {n m : ℕ} (h₁ : n < m) : ¬ m < n :=
  le_lt_antisymm (nat.le_of_lt h₁)

  theorem not_lt_zero (a : ℕ) : ¬ a < 0 := not_succ_le_zero a

  attribute [simp]
  theorem lt_zero_iff_false (a : ℕ) : a < 0 ↔ false :=
  iff_false_intro (not_lt_zero a)

  protected theorem eq_or_lt_of_le {a b : ℕ} (h : a ≤ b) : a = b ∨ a < b :=
  le.cases_on h (or.inl rfl) (λ n h, or.inr (succ_le_succ h))

  protected theorem le_of_eq_or_lt {a b : ℕ} (h : a = b ∨ a < b) : a ≤ b :=
  or.elim h nat.le_of_eq nat.le_of_lt

  theorem succ_lt_succ {a b : ℕ} : a < b → succ a < succ b :=
  succ_le_succ

  theorem lt_of_succ_lt {a b : ℕ} : succ a < b → a < b :=
  le_of_succ_le

  theorem lt_of_succ_lt_succ {a b : ℕ} : succ a < succ b → a < b :=
  le_of_succ_le_succ

  instance decidable_le : ∀ a b : ℕ, decidable (a ≤ b)
  | 0     b     := is_true (zero_le b)
  | (a+1) 0     := is_false (not_succ_le_zero a)
  | (a+1) (b+1) :=
    match decidable_le a b with
    | is_true h  := is_true (succ_le_succ h)
    | is_false h := is_false (λ a, h (le_of_succ_le_succ a))
    end

  instance decidable_lt : ∀ a b : ℕ, decidable (a < b) :=
  λ a b, nat.decidable_le (succ a) b

  protected theorem lt_or_ge : ∀ (a b : ℕ), a < b ∨ a ≥ b
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

  protected definition {u} lt_ge_by_cases {a b : ℕ} {C : Type u} (h₁ : a < b → C) (h₂ : a ≥ b → C) : C :=
  decidable.by_cases h₁ (λ h, h₂ (or.elim (nat.lt_or_ge a b) (λ a, absurd a h) (λ a, a)))

  protected definition {u} lt_by_cases {a b : ℕ} {C : Type u} (h₁ : a < b → C) (h₂ : a = b → C)
    (h₃ : b < a → C) : C :=
  nat.lt_ge_by_cases h₁ (λ h₁,
    nat.lt_ge_by_cases h₃ (λ h, h₂ (nat.le_antisymm h h₁)))

  protected theorem lt_trichotomy (a b : ℕ) : a < b ∨ a = b ∨ b < a :=
  nat.lt_by_cases (λ h, or.inl h) (λ h, or.inr (or.inl h)) (λ h, or.inr (or.inr h))

  protected theorem eq_or_lt_of_not_lt {a b : ℕ} (hnlt : ¬ a < b) : a = b ∨ b < a :=
  or.elim (nat.lt_trichotomy a b)
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
  theorem zero_sub_eq_zero : ∀ a : ℕ, 0 - a = 0
  | 0     := rfl
  | (a+1) := congr_arg pred (zero_sub_eq_zero a)

  theorem zero_eq_zero_sub (a : ℕ) : 0 = 0 - a :=
  eq.symm (zero_sub_eq_zero a)

  theorem sub_le (a b : ℕ) : a - b ≤ a :=
  nat.rec_on b (nat.le_refl (a - 0)) (λ b₁, nat.le_trans (pred_le (a - b₁)))

  attribute [simp]
  theorem sub_le_iff_true (a b : ℕ) : a - b ≤ a ↔ true :=
  iff_true_intro (sub_le a b)

  theorem sub_lt : ∀ {a b : ℕ}, 0 < a → 0 < b → a - b < a
  | 0     b     h1 h2 := absurd h1 (nat.lt_irrefl 0)
  | (a+1) 0     h1 h2 := absurd h2 (nat.lt_irrefl 0)
  | (a+1) (b+1) h1 h2 :=
    eq.symm (succ_sub_succ_eq_sub a b) ▸
      show a - b < succ a, from
      lt_succ_of_le (sub_le a b)

  theorem sub_lt_succ (a b : ℕ) : a - b < succ a :=
  lt_succ_of_le (sub_le a b)

  attribute [simp]
  theorem sub_lt_succ_iff_true (a b : ℕ) : a - b < succ a ↔ true :=
  iff_true_intro (sub_lt_succ a b)

  theorem le_add_right : ∀ (n k : ℕ), n ≤ n + k
  | n 0     := nat.le_refl n
  | n (k+1) := le_succ_of_le (le_add_right n k)

  theorem le_add_left (n m : ℕ): n ≤ m + n :=
  nat.add_comm n m ▸ le_add_right n m

  definition {u} repeat {A : Type u} (f : ℕ → A → A) : ℕ → A → A
  | 0         a := a
  | (succ n)  a := f n (repeat n a)

  instance : inhabited ℕ :=
  ⟨nat.zero⟩
end nat
