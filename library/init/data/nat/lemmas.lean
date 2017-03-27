/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad
-/
prelude
import init.data.nat.basic init.data.nat.div init.data.nat.pow init.meta init.algebra.functions

namespace nat
attribute [pre_smt] nat_zero_eq_zero

protected lemma zero_add : ∀ n : ℕ, 0 + n = n
| 0     := rfl
| (n+1) := congr_arg succ (zero_add n)

lemma succ_add : ∀ n m : ℕ, (succ n) + m = succ (n + m)
| n 0     := rfl
| n (m+1) := congr_arg succ (succ_add n m)

lemma add_succ : ∀ n m : ℕ, n + succ m = succ (n + m) :=
λ n m, rfl

protected lemma add_zero : ∀ n : ℕ, n + 0 = n :=
λ n, rfl

lemma add_one_eq_succ : ∀ n : ℕ, n + 1 = succ n :=
λ n, rfl

protected lemma add_comm : ∀ n m : ℕ, n + m = m + n
| n 0     := eq.symm (nat.zero_add n)
| n (m+1) :=
  suffices succ (n + m) = succ (m + n), from
    eq.symm (succ_add m n) ▸ this,
  congr_arg succ (add_comm n m)

protected lemma add_assoc : ∀ n m k : ℕ, (n + m) + k = n + (m + k)
| n m 0        := rfl
| n m (succ k) := by simp [add_succ, add_assoc n m k]

protected lemma add_left_comm : ∀ (n m k : ℕ), n + (m + k) = m + (n + k) :=
left_comm nat.add nat.add_comm nat.add_assoc

protected lemma add_left_cancel : ∀ {n m k : ℕ}, n + m = n + k → m = k
| 0        m k := by simp [nat.zero_add] {contextual := tt}
| (succ n) m k := λ h,
  have n+m = n+k, begin simp [succ_add] at h, injection h, assumption end,
  add_left_cancel this

protected lemma add_right_cancel {n m k : ℕ} (h : n + m = k + m) : n = k :=
have m + n = m + k, begin rw [nat.add_comm n m, nat.add_comm k m] at h, assumption end,
nat.add_left_cancel this

lemma succ_ne_zero (n : ℕ) : succ n ≠ 0 :=
assume h, nat.no_confusion h

lemma succ_ne_self : ∀ n : ℕ, succ n ≠ n
| 0     h := absurd h (nat.succ_ne_zero 0)
| (n+1) h := succ_ne_self n (nat.no_confusion h (λ h, h))

protected lemma one_ne_zero : 1 ≠ (0 : ℕ) :=
assume h, nat.no_confusion h

protected lemma zero_ne_one : 0 ≠ (1 : ℕ) :=
assume h, nat.no_confusion h

instance : zero_ne_one_class ℕ :=
{ zero := 0, one := 1, zero_ne_one := nat.zero_ne_one }

lemma eq_zero_of_add_eq_zero_right : ∀ {n m : ℕ}, n + m = 0 → n = 0
| 0     m := by simp [nat.zero_add]
| (n+1) m := λ h,
  begin
    exfalso,
    rw [add_one_eq_succ, succ_add] at h,
    apply succ_ne_zero _ h
  end

lemma eq_zero_of_add_eq_zero_left {n m : ℕ} (h : n + m = 0) : m = 0 :=
@eq_zero_of_add_eq_zero_right m n (nat.add_comm n m ▸ h)

@[simp]
lemma pred_zero : pred 0 = 0 :=
rfl

@[simp]
lemma pred_succ (n : ℕ) : pred (succ n) = n :=
rfl

protected lemma mul_zero (n : ℕ) : n * 0 = 0 :=
rfl

lemma mul_succ (n m : ℕ) : n * succ m = n * m + n :=
rfl

protected theorem zero_mul : ∀ (n : ℕ), 0 * n = 0
| 0        := rfl
| (succ n) := by rw [mul_succ, zero_mul]

private meta def sort_add :=
`[simp [nat.add_assoc, nat.add_comm, nat.add_left_comm]]

lemma succ_mul : ∀ (n m : ℕ), (succ n) * m = (n * m) + m
| n 0        := rfl
| n (succ m) :=
  begin
    simp [mul_succ, add_succ, succ_mul n m],
    sort_add
  end

protected lemma right_distrib : ∀ (n m k : ℕ), (n + m) * k = n * k + m * k
| n m 0        := rfl
| n m (succ k) :=
  begin simp [mul_succ, right_distrib n m k], sort_add end

protected lemma left_distrib : ∀ (n m k : ℕ), n * (m + k) = n * m + n * k
| 0        m k := by simp [nat.zero_mul]
| (succ n) m k :=
  begin simp [succ_mul, left_distrib n m k], sort_add end

protected lemma mul_comm : ∀ (n m : ℕ), n * m = m * n
| n 0        := by rw [nat.zero_mul, nat.mul_zero]
| n (succ m) := by simp [mul_succ, succ_mul, mul_comm n m]

protected lemma mul_assoc : ∀ (n m k : ℕ), (n * m) * k = n * (m * k)
| n m 0        := rfl
| n m (succ k) := by simp [mul_succ, nat.left_distrib, mul_assoc n m k]

protected lemma mul_one : ∀ (n : ℕ), n * 1 = n
| 0        := rfl
| (succ n) := by simp [succ_mul, mul_one n, add_one_eq_succ]

protected lemma one_mul (n : ℕ) : 1 * n = n :=
by rw [nat.mul_comm, nat.mul_one]

lemma eq_zero_or_eq_zero_of_mul_eq_zero : ∀ {n m : ℕ}, n * m = 0 → n = 0 ∨ m = 0
| 0        m := λ h, or.inl rfl
| (succ n) m :=
  begin
    rw succ_mul, intro h,
    exact or.inr (eq_zero_of_add_eq_zero_left h)
  end

instance : comm_semiring nat :=
{add            := nat.add,
 add_assoc      := nat.add_assoc,
 zero           := nat.zero,
 zero_add       := nat.zero_add,
 add_zero       := nat.add_zero,
 add_comm       := nat.add_comm,
 mul            := nat.mul,
 mul_assoc      := nat.mul_assoc,
 one            := nat.succ nat.zero,
 one_mul        := nat.one_mul,
 mul_one        := nat.mul_one,
 left_distrib   := nat.left_distrib,
 right_distrib  := nat.right_distrib,
 zero_mul       := nat.zero_mul,
 mul_zero       := nat.mul_zero,
 mul_comm       := nat.mul_comm}

/- properties of inequality -/

protected lemma le_of_eq {n m : ℕ} (p : n = m) : n ≤ m :=
p ▸ less_than_or_equal.refl n

lemma le_succ_iff_true (n : ℕ) : n ≤ succ n ↔ true :=
iff_true_intro (le_succ n)

lemma pred_le_iff_true (n : ℕ) : pred n ≤ n ↔ true :=
iff_true_intro (pred_le n)

lemma le_succ_of_le {n m : ℕ} (h : n ≤ m) : n ≤ succ m :=
nat.le_trans h (le_succ m)

lemma le_of_succ_le {n m : ℕ} (h : succ n ≤ m) : n ≤ m :=
nat.le_trans (le_succ n) h

protected lemma le_of_lt {n m : ℕ} (h : n < m) : n ≤ m :=
le_of_succ_le h

lemma le_succ_of_pred_le {n m : ℕ} : pred n ≤ m → n ≤ succ m :=
nat.cases_on n less_than_or_equal.step (λ a, succ_le_succ)

lemma succ_le_zero_iff_false (n : ℕ) : succ n ≤ 0 ↔ false :=
iff_false_intro (not_succ_le_zero n)

lemma succ_le_self_iff_false (n : ℕ) : succ n ≤ n ↔ false :=
iff_false_intro (not_succ_le_self n)

lemma zero_le_iff_true (n : ℕ) : 0 ≤ n ↔ true :=
iff_true_intro (zero_le n)

def lt.step {n m : ℕ} : n < m → n < succ m := less_than_or_equal.step

lemma zero_lt_succ_iff_true (n : ℕ) : 0 < succ n ↔ true :=
iff_true_intro (zero_lt_succ n)

def succ_pos_iff_true := zero_lt_succ_iff_true

protected lemma pos_of_ne_zero {n : nat} (h : n ≠ 0) : n > 0 :=
begin cases n, contradiction, apply succ_pos end

protected lemma lt_trans {n m k : ℕ} (h₁ : n < m) : m < k → n < k :=
nat.le_trans (less_than_or_equal.step h₁)

protected lemma lt_of_le_of_lt {n m k : ℕ} (h₁ : n ≤ m) : m < k → n < k :=
nat.le_trans (succ_le_succ h₁)

lemma lt_self_iff_false (n : ℕ) : n < n ↔ false :=
iff_false_intro (λ h, absurd h (nat.lt_irrefl n))

lemma self_lt_succ (n : ℕ) : n < succ n := nat.le_refl (succ n)

def lt_succ_self := @self_lt_succ

lemma self_lt_succ_iff_true (n : ℕ) : n < succ n ↔ true :=
iff_true_intro (self_lt_succ n)

def lt_succ_self_iff_true := @self_lt_succ_iff_true

def lt.base (n : ℕ) : n < succ n := nat.le_refl (succ n)

lemma le_lt_antisymm {n m : ℕ} (h₁ : n ≤ m) (h₂ : m < n) : false :=
nat.lt_irrefl n (nat.lt_of_le_of_lt h₁ h₂)

protected lemma le_antisymm {n m : ℕ} (h₁ : n ≤ m) : m ≤ n → n = m :=
less_than_or_equal.cases_on h₁ (λ a, rfl) (λ a b c, absurd (nat.lt_of_le_of_lt b c) (nat.lt_irrefl n))

instance : weak_order ℕ :=
⟨@nat.less_than_or_equal, @nat.le_refl, @nat.le_trans, @nat.le_antisymm⟩

lemma lt_le_antisymm {n m : ℕ} (h₁ : n < m) (h₂ : m ≤ n) : false :=
le_lt_antisymm h₂ h₁

protected lemma nat.lt_asymm {n m : ℕ} (h₁ : n < m) : ¬ m < n :=
le_lt_antisymm (nat.le_of_lt h₁)

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

protected def {u} lt_ge_by_cases {a b : ℕ} {C : Sort u} (h₁ : a < b → C) (h₂ : a ≥ b → C) : C :=
decidable.by_cases h₁ (λ h, h₂ (or.elim (nat.lt_or_ge a b) (λ a, absurd a h) (λ a, a)))

protected def {u} lt_by_cases {a b : ℕ} {C : Sort u} (h₁ : a < b → C) (h₂ : a = b → C)
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

lemma le_add_right : ∀ (n k : ℕ), n ≤ n + k
| n 0     := nat.le_refl n
| n (k+1) := le_succ_of_le (le_add_right n k)

lemma le_add_left (n m : ℕ): n ≤ m + n :=
nat.add_comm n m ▸ le_add_right n m

lemma le.dest : ∀ {n m : ℕ}, n ≤ m → ∃ k, n + k = m
| n ._ (less_than_or_equal.refl ._)  := ⟨0, rfl⟩
| n ._ (@less_than_or_equal.step ._ m h) :=
  match le.dest h with
  | ⟨w, hw⟩ := ⟨succ w, hw ▸ add_succ n w⟩
  end

lemma le.intro {n m k : ℕ} (h : n + k = m) : n ≤ m :=
h ▸ le_add_right n k

protected lemma add_le_add_left {n m : ℕ} (h : n ≤ m) (k : ℕ) : k + n ≤ k + m :=
match le.dest h with
| ⟨w, hw⟩ := @le.intro _ _ w begin rw [nat.add_assoc, hw] end
end

protected lemma add_le_add_right {n m : ℕ} (h : n ≤ m) (k : ℕ) : n + k ≤ m + k :=
begin rw [nat.add_comm n k, nat.add_comm m k], apply nat.add_le_add_left h end

protected lemma le_of_add_le_add_left {k n m : ℕ} (h : k + n ≤ k + m) : n ≤ m :=
match le.dest h with
| ⟨w, hw⟩ := @le.intro _ _ w
  begin
    dsimp at hw,
    rw [nat.add_assoc] at hw,
    apply nat.add_left_cancel hw
  end
end

protected lemma le_of_add_le_add_right {k n m : ℕ} : n + k ≤ m + k → n ≤ m :=
begin
  rw [nat.add_comm _ k,nat.add_comm _ k],
  apply nat.le_of_add_le_add_left
end

protected lemma add_le_add_iff_le_right (k n m : ℕ) : n + k ≤ m + k ↔ n ≤ m :=
  ⟨ nat.le_of_add_le_add_right , take h, nat.add_le_add_right h _ ⟩

protected lemma lt_of_le_and_ne {m n : ℕ} (h1 : m ≤ n) : m ≠ n → m < n :=
or.resolve_right (or.swap (nat.eq_or_lt_of_le h1))

protected theorem lt_of_add_lt_add_left {k n m : ℕ} (h : k + n < k + m) : n < m :=
let h' := nat.le_of_lt h in
nat.lt_of_le_and_ne
  (nat.le_of_add_le_add_left h')
  (λ heq, nat.lt_irrefl (k + m) begin rw heq at h, assumption end)

protected lemma add_lt_add_left {n m : ℕ} (h : n < m) (k : ℕ) : k + n < k + m :=
lt_of_succ_le (add_succ k n ▸ nat.add_le_add_left (succ_le_of_lt h) k)

protected lemma add_lt_add_right {n m : ℕ} (h : n < m) (k : ℕ) : n + k < m + k :=
nat.add_comm k m ▸ nat.add_comm k n ▸ nat.add_lt_add_left h k

protected lemma lt_add_of_pos_right {n k : ℕ} (h : k > 0) : n < n + k :=
nat.add_lt_add_left h n

protected lemma zero_lt_one : 0 < (1:nat) :=
zero_lt_succ 0

def one_pos := nat.zero_lt_one

protected lemma le_total {m n : ℕ} : m ≤ n ∨ n ≤ m :=
or.imp_left nat.le_of_lt (nat.lt_or_ge m n)

protected lemma le_of_lt_or_eq {m n : ℕ} (h : m < n ∨ m = n) : m ≤ n :=
nat.le_of_eq_or_lt (or.swap h)

protected lemma lt_or_eq_of_le {m n : ℕ} (h : m ≤ n) : m < n ∨ m = n :=
or.swap (nat.eq_or_lt_of_le h)

protected lemma le_iff_lt_or_eq (m n : ℕ) : m ≤ n ↔ m < n ∨ m = n :=
iff.intro nat.lt_or_eq_of_le nat.le_of_lt_or_eq

lemma mul_le_mul_left {n m : ℕ} (k : ℕ) (h : n ≤ m) : k * n ≤ k * m :=
match le.dest h with
| ⟨l, hl⟩ :=
  have k * n + k * l = k * m, by rw [-left_distrib, hl],
  le.intro this
end

lemma mul_le_mul_right {n m : ℕ} (k : ℕ) (h : n ≤ m) : n * k ≤ m * k :=
mul_comm k m ▸ mul_comm k n ▸ mul_le_mul_left k h

protected lemma mul_lt_mul_of_pos_left {n m k : ℕ} (h : n < m) (hk : k > 0) : k * n < k * m :=
nat.lt_of_lt_of_le (nat.lt_add_of_pos_right hk) (mul_succ k n ▸ nat.mul_le_mul_left k (succ_le_of_lt h))

protected lemma mul_lt_mul_of_pos_right {n m k : ℕ} (h : n < m) (hk : k > 0) : n * k < m * k :=
mul_comm k m ▸ mul_comm k n ▸ nat.mul_lt_mul_of_pos_left h hk

instance : decidable_linear_ordered_semiring nat :=
{ nat.comm_semiring with
  add_left_cancel            := @nat.add_left_cancel,
  add_right_cancel           := @nat.add_right_cancel,
  lt                         := nat.lt,
  le                         := nat.le,
  le_refl                    := nat.le_refl,
  le_trans                   := @nat.le_trans,
  le_antisymm                := @nat.le_antisymm,
  le_total                   := @nat.le_total,
  le_iff_lt_or_eq            := @nat.le_iff_lt_or_eq,
  le_of_lt                   := @nat.le_of_lt,
  lt_irrefl                  := @nat.lt_irrefl,
  lt_of_lt_of_le             := @nat.lt_of_lt_of_le,
  lt_of_le_of_lt             := @nat.lt_of_le_of_lt,
  lt_of_add_lt_add_left      := @nat.lt_of_add_lt_add_left,
  add_lt_add_left            := @nat.add_lt_add_left,
  add_le_add_left            := @nat.add_le_add_left,
  le_of_add_le_add_left      := @nat.le_of_add_le_add_left,
  zero_lt_one                := zero_lt_succ 0,
  mul_le_mul_of_nonneg_left  := (take a b c h₁ h₂, nat.mul_le_mul_left c h₁),
  mul_le_mul_of_nonneg_right := (take a b c h₁ h₂, nat.mul_le_mul_right c h₁),
  mul_lt_mul_of_pos_left     := @nat.mul_lt_mul_of_pos_left,
  mul_lt_mul_of_pos_right    := @nat.mul_lt_mul_of_pos_right,
  decidable_lt               := nat.decidable_lt,
  decidable_le               := nat.decidable_le,
  decidable_eq               := nat.decidable_eq }

lemma le_of_lt_succ {m n : nat} : m < succ n → m ≤ n :=
le_of_succ_le_succ

/- sub properties -/

lemma sub_eq_succ_sub_succ (a b : ℕ) : a - b = succ a - succ b :=
eq.symm (succ_sub_succ_eq_sub a b)

lemma zero_sub_eq_zero : ∀ a : ℕ, 0 - a = 0
| 0     := rfl
| (a+1) := congr_arg pred (zero_sub_eq_zero a)

lemma zero_eq_zero_sub (a : ℕ) : 0 = 0 - a :=
eq.symm (zero_sub_eq_zero a)

lemma sub_le_iff_true (a b : ℕ) : a - b ≤ a ↔ true :=
iff_true_intro (sub_le a b)

lemma sub_lt_succ (a b : ℕ) : a - b < succ a :=
lt_succ_of_le (sub_le a b)

lemma sub_lt_succ_iff_true (a b : ℕ) : a - b < succ a ↔ true :=
iff_true_intro (sub_lt_succ a b)

protected theorem sub_le_sub_right {n m : ℕ} (h : n ≤ m) : ∀ k, n - k ≤ m - k
| 0        := h
| (succ z) := pred_le_pred (sub_le_sub_right z)

/- bit0/bit1 properties -/

protected lemma bit0_succ_eq (n : ℕ) : bit0 (succ n) = succ (succ (bit0 n)) :=
show succ (succ n + n) = succ (succ (n + n)), from
congr_arg succ (succ_add n n)

protected lemma bit1_eq_succ_bit0 (n : ℕ) : bit1 n = succ (bit0 n) :=
rfl

protected lemma bit1_succ_eq (n : ℕ) : bit1 (succ n) = succ (succ (bit1 n)) :=
eq.trans (nat.bit1_eq_succ_bit0 (succ n)) (congr_arg succ (nat.bit0_succ_eq n))

protected lemma bit0_ne_zero : ∀ {n : ℕ}, n ≠ 0 → bit0 n ≠ 0
| 0     h := absurd rfl h
| (n+1) h := succ_ne_zero _

protected lemma bit1_ne_zero (n : ℕ) : bit1 n ≠ 0 :=
show succ (n + n) ≠ 0, from
succ_ne_zero (n + n)

protected lemma bit1_ne_one : ∀ {n : ℕ}, n ≠ 0 → bit1 n ≠ 1
| 0     h h1 := absurd rfl h
| (n+1) h h1 := nat.no_confusion h1 (λ h2, absurd h2 (succ_ne_zero _))

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

protected lemma bit0_ne_bit1 : ∀ (n m : ℕ), bit0 n ≠ bit1 m :=
λ n m : nat, ne.symm (nat.bit1_ne_bit0 m n)

protected lemma bit0_inj : ∀ {n m : ℕ}, bit0 n = bit0 m → n = m
| 0     0     h := rfl
| 0     (m+1) h := by contradiction
| (n+1) 0     h := by contradiction
| (n+1) (m+1) h :=
  have succ (succ (n + n)) = succ (succ (m + m)),
  begin unfold bit0 at h, simp [add_one_eq_succ, add_succ, succ_add] at h, exact h end,
  have n + n = m + m, begin repeat {injection this with this}, assumption end,
  have n = m, from bit0_inj this,
  by rw this

protected lemma bit1_inj : ∀ {n m : ℕ}, bit1 n = bit1 m → n = m :=
λ n m h,
have succ (bit0 n) = succ (bit0 m), begin simp [nat.bit1_eq_succ_bit0] at h, assumption end,
have bit0 n = bit0 m, from begin injection this, assumption end,
nat.bit0_inj this

protected lemma bit0_ne {n m : ℕ} : n ≠ m → bit0 n ≠ bit0 m :=
λ h₁ h₂, absurd (nat.bit0_inj h₂) h₁

protected lemma bit1_ne {n m : ℕ} : n ≠ m → bit1 n ≠ bit1 m :=
λ h₁ h₂, absurd (nat.bit1_inj h₂) h₁

protected lemma zero_ne_bit0 {n : ℕ} : n ≠ 0 → 0 ≠ bit0 n :=
λ h, ne.symm (nat.bit0_ne_zero h)

protected lemma zero_ne_bit1 (n : ℕ) : 0 ≠ bit1 n :=
ne.symm (nat.bit1_ne_zero n)

protected lemma one_ne_bit0 (n : ℕ) : 1 ≠ bit0 n :=
ne.symm (nat.bit0_ne_one n)

protected lemma one_ne_bit1 {n : ℕ} : n ≠ 0 → 1 ≠ bit1 n :=
λ h, ne.symm (nat.bit1_ne_one h)

protected lemma zero_lt_bit1 (n : nat) : 0 < bit1 n :=
zero_lt_succ _

protected lemma zero_lt_bit0 : ∀ {n : nat}, n ≠ 0 → 0 < bit0 n
| 0        h := by contradiction
| (succ n) h :=
  begin
    rw nat.bit0_succ_eq,
    apply zero_lt_succ
  end

protected lemma one_lt_bit1 : ∀ {n : nat}, n ≠ 0 → 1 < bit1 n
| 0        h := by contradiction
| (succ n) h :=
  begin
    rw nat.bit1_succ_eq,
    apply succ_lt_succ,
    apply zero_lt_succ
  end

protected lemma one_lt_bit0 : ∀ {n : nat}, n ≠ 0 → 1 < bit0 n
| 0        h := by contradiction
| (succ n) h :=
  begin
    rw nat.bit0_succ_eq,
    apply succ_lt_succ,
    apply zero_lt_succ
  end

protected lemma bit0_lt {n m : nat} (h : n < m) : bit0 n < bit0 m :=
add_lt_add h h

protected lemma bit1_lt {n m : nat} (h : n < m) : bit1 n < bit1 m :=
succ_lt_succ (add_lt_add h h)

protected lemma bit0_lt_bit1 {n m : nat} (h : n ≤ m) : bit0 n < bit1 m :=
lt_succ_of_le (add_le_add h h)

protected lemma bit1_lt_bit0 : ∀ {n m : nat}, n < m → bit1 n < bit0 m
| n 0        h := absurd h (not_lt_zero _)
| n (succ m) h :=
  have n ≤ m, from le_of_lt_succ h,
  have succ (n + n) ≤ succ (m + m), from succ_le_succ (add_le_add this this),
  have succ (n + n) ≤ succ m + m, {rw succ_add, assumption},
  show succ (n + n) < succ (succ m + m), from lt_succ_of_le this

protected lemma one_le_bit1 (n : ℕ) : 1 ≤ bit1 n :=
show 1 ≤ succ (bit0 n), from
succ_le_succ (zero_le (bit0 n))

protected lemma one_le_bit0 : ∀ (n : ℕ), n ≠ 0 → 1 ≤ bit0 n
| 0     h := absurd rfl h
| (n+1) h :=
  suffices 1 ≤ succ (succ (bit0 n)), from
    eq.symm (nat.bit0_succ_eq n) ▸ this,
  succ_le_succ (zero_le (succ (bit0 n)))

/- Extra instances to short-circuit type class resolution -/
instance : add_comm_monoid nat    := by apply_instance
instance : add_monoid nat         := by apply_instance
instance : monoid nat             := by apply_instance
instance : comm_monoid nat        := by apply_instance
instance : comm_semigroup nat     := by apply_instance
instance : semigroup nat          := by apply_instance
instance : add_comm_semigroup nat := by apply_instance
instance : add_semigroup nat      := by apply_instance
instance : distrib nat            := by apply_instance
instance : semiring nat           := by apply_instance
instance : ordered_semiring nat   := by apply_instance

/- subtraction -/
@[simp]
protected theorem sub_zero (n : ℕ) : n - 0 = n :=
rfl

theorem sub_succ (n m : ℕ) : n - succ m = pred (n - m) :=
rfl

protected theorem zero_sub : ∀ (n : ℕ), 0 - n = 0
| 0        := by rw nat.sub_zero
| (succ n) := by rw [nat.sub_succ, zero_sub n, pred_zero]

theorem succ_sub_succ (n m : ℕ) : succ n - succ m = n - m :=
succ_sub_succ_eq_sub n m

protected theorem sub_self : ∀ (n : ℕ), n - n = 0
| 0        := by rw nat.sub_zero
| (succ n) := by rw [succ_sub_succ, sub_self n]

/- TODO(Leo): remove the following ematch annotations as soon as we have
   arithmetic theory in the smt_stactic -/
@[ematch_lhs]
protected theorem add_sub_add_right : ∀ (n k m : ℕ), (n + k) - (m + k) = n - m
| n 0        m := by rw [add_zero, add_zero]
| n (succ k) m := by rw [add_succ, add_succ, succ_sub_succ, add_sub_add_right n k m]

@[ematch_lhs]
protected theorem add_sub_add_left (k n m : ℕ) : (k + n) - (k + m) = n - m :=
by rw [add_comm k n, add_comm k m, nat.add_sub_add_right]

@[ematch_lhs]
protected theorem add_sub_cancel (n m : ℕ) : n + m - m = n :=
suffices n + m - (0 + m) = n, from
  by rwa [zero_add] at this,
by rw [nat.add_sub_add_right, nat.sub_zero]

@[ematch_lhs]
protected theorem add_sub_cancel_left (n m : ℕ) : n + m - n = m :=
show n + m - (n + 0) = m, from
by rw [nat.add_sub_add_left, nat.sub_zero]

protected theorem sub_sub : ∀ (n m k : ℕ), n - m - k = n - (m + k)
| n m 0        := by rw [add_zero, nat.sub_zero]
| n m (succ k) := by rw [add_succ, nat.sub_succ, nat.sub_succ, sub_sub n m k]

theorem succ_sub_sub_succ (n m k : ℕ) : succ n - m - succ k = n - m - k :=
by rw [nat.sub_sub, nat.sub_sub, add_succ, succ_sub_succ]

theorem le_of_le_of_sub_le_sub_right {n m k : ℕ}
  (h₀ : k ≤ m)
  (h₁ : n - k ≤ m - k)
: n ≤ m :=
begin
  revert k m,
  induction n with n ; intros k m h₀ h₁,
  { apply zero_le },
  { cases k with k,
    { apply h₁ },
    cases m with m,
    { cases not_succ_le_zero _ h₀ },
    { simp [succ_sub_succ] at h₁,
      apply succ_le_succ,
      apply ih_1 _ h₁,
      apply le_of_succ_le_succ h₀ }, }
end

protected theorem sub_le_sub_right_iff (n m k : ℕ)
  (h : k ≤ m)
: n - k ≤ m - k ↔ n ≤ m :=
⟨ le_of_le_of_sub_le_sub_right h , assume h, nat.sub_le_sub_right h k ⟩

theorem sub_self_add (n m : ℕ) : n - (n + m) = 0 :=
show (n + 0) - (n + m) = 0, from
by rw [nat.add_sub_add_left, nat.zero_sub]

theorem add_le_to_le_sub (x : ℕ) {y k : ℕ}
  (h : k ≤ y)
: x + k ≤ y ↔ x ≤ y - k :=
by rw [-nat.add_sub_cancel x k,nat.sub_le_sub_right_iff _ _ _ h,nat.add_sub_cancel]

lemma sub_lt_of_pos_le (a b : ℕ) (h₀ : 0 < a) (h₁ : a ≤ b)
: b - a < b :=
begin
  apply sub_lt _ h₀,
  apply lt_of_lt_of_le h₀ h₁
end

protected theorem sub.right_comm (m n k : ℕ) : m - n - k = m - k - n :=
by rw [nat.sub_sub, nat.sub_sub, add_comm]

theorem sub_one (n : ℕ) : n - 1 = pred n :=
rfl

theorem succ_sub_one (n : ℕ) : succ n - 1 = n :=
rfl

theorem succ_pred_eq_of_pos : ∀ {n : ℕ}, n > 0 → succ (pred n) = n
| 0 h        := absurd h (lt_irrefl 0)
| (succ k) h := rfl

theorem mul_pred_left : ∀ (n m : ℕ), pred n * m = n * m - m
| 0        m := by simp [nat.zero_sub, pred_zero, zero_mul]
| (succ n) m := by rw [pred_succ, succ_mul, nat.add_sub_cancel]

theorem mul_pred_right (n m : ℕ) : n * pred m = n * m - n :=
by rw [mul_comm, mul_pred_left, mul_comm]

protected theorem mul_sub_right_distrib : ∀ (n m k : ℕ), (n - m) * k = n * k - m * k
| n 0        k := by simp [nat.sub_zero]
| n (succ m) k := by rw [nat.sub_succ, mul_pred_left, mul_sub_right_distrib, succ_mul, nat.sub_sub]

protected theorem mul_sub_left_distrib (n m k : ℕ) : n * (m - k) = n * m - n * k :=
by rw [mul_comm, nat.mul_sub_right_distrib, mul_comm m n, mul_comm n k]

protected theorem mul_self_sub_mul_self_eq (a b : nat) : a * a - b * b = (a + b) * (a - b) :=
by rw [nat.mul_sub_left_distrib, right_distrib, right_distrib, mul_comm b a, add_comm (a*a) (a*b),
       nat.add_sub_add_left]

theorem succ_mul_succ_eq (a : nat) : succ a * succ a = a*a + a + a + 1 :=
begin rw [-add_one_eq_succ], simp [right_distrib, left_distrib] end

theorem sub_eq_zero_of_le {n m : ℕ} (h : n ≤ m) : n - m = 0 :=
exists.elim (nat.le.dest h)
  (take k, assume hk : n + k = m, by rw [-hk, sub_self_add])

protected theorem le_of_sub_eq_zero : ∀{n m : ℕ}, n - m = 0 → n ≤ m
| n 0 H := begin rw [nat.sub_zero] at H, simp [H] end
| 0 (m+1) H := zero_le _
| (n+1) (m+1) H := add_le_add_right
  (le_of_sub_eq_zero begin simp [nat.add_sub_add_right] at H, exact H end) _

protected theorem sub_eq_zero_iff_le {n m : ℕ} : n - m = 0 ↔ n ≤ m :=
⟨nat.le_of_sub_eq_zero, nat.sub_eq_zero_of_le⟩

theorem succ_sub {m n : ℕ} (h : m ≥ n) : succ m - n  = succ (m - n) :=
exists.elim (nat.le.dest h)
  (take k, assume hk : n + k = m,
    by rw [-hk, nat.add_sub_cancel_left, -add_succ, nat.add_sub_cancel_left])

theorem add_sub_of_le {n m : ℕ} (h : n ≤ m) : n + (m - n) = m :=
exists.elim (nat.le.dest h)
  (take k, assume hk : n + k = m,
    by rw [-hk, nat.add_sub_cancel_left])

protected theorem sub_add_cancel {n m : ℕ} (h : n ≥ m) : n - m + m = n :=
by rw [add_comm, add_sub_of_le h]

protected theorem sub_pos_of_lt {m n : ℕ} (h : m < n) : n - m > 0 :=
have 0 + m < n - m + m, begin rw [zero_add, nat.sub_add_cancel (le_of_lt h)], exact h end,
lt_of_add_lt_add_right this

protected theorem add_sub_assoc {m k : ℕ} (h : k ≤ m) (n : ℕ) : n + m - k = n + (m - k) :=
exists.elim (nat.le.dest h)
  (take l, assume hl : k + l = m,
    by rw [-hl, nat.add_sub_cancel_left, add_comm k, -add_assoc, nat.add_sub_cancel])

protected lemma sub_eq_iff_eq_add {a b c : ℕ} (ab : b ≤ a) : a - b = c ↔ a = c + b :=
⟨take c_eq, begin rw [c_eq.symm, nat.sub_add_cancel ab] end,
  take a_eq, begin rw [a_eq, nat.add_sub_cancel] end⟩

protected lemma lt_of_sub_eq_succ {m n l : ℕ} (H : m - n = nat.succ l) : n < m :=
lt_of_not_ge
  (take (H' : n ≥ m), begin simp [nat.sub_eq_zero_of_le H'] at H, contradiction end)

@[simp] lemma min_zero_left (a : ℕ) : min 0 a = 0 :=
min_eq_left (zero_le a)

@[simp] lemma min_zero_right (a : ℕ) : min a 0 = 0 :=
min_eq_right (zero_le a)

theorem zero_min (a : ℕ) : min 0 a = 0 :=
min_zero_left a

theorem min_zero (a : ℕ) : min a 0 = 0 :=
min_zero_right a

-- Distribute succ over min
lemma min_succ_succ (x y : ℕ) : min (succ x) (succ y) = succ (min x y) :=
have f : x ≤ y → min (succ x) (succ y) = succ (min x y), from λp,
  calc min (succ x) (succ y)
              = succ x         : if_pos (succ_le_succ p)
          ... = succ (min x y) : congr_arg succ (eq.symm (if_pos p)),
have g : ¬ (x ≤ y) → min (succ x) (succ y) = succ (min x y), from λp,
  calc min (succ x) (succ y)
              = succ y         : if_neg (λeq, p (pred_le_pred eq))
          ... = succ (min x y) : congr_arg succ (eq.symm (if_neg p)),
decidable.by_cases f g

lemma sub_eq_sub_min (n m : ℕ) : n - m = n - min n m :=
if h : n ≥ m then by rewrite [min_eq_right h]
else by rewrite [sub_eq_zero_of_le (le_of_not_ge h), min_eq_left (le_of_not_ge h), nat.sub_self]

@[simp]
lemma sub_add_min_cancel (n m : ℕ) : n - m + min n m = n :=
by rewrite [sub_eq_sub_min, nat.sub_add_cancel (min_le_left n m)]

lemma pred_inj : ∀ {a b : nat}, a > 0 → b > 0 → nat.pred a = nat.pred b → a = b
| (succ a) (succ b) ha hb h := have a = b, from h, by rw this
| (succ a) 0        ha hb h := absurd hb (lt_irrefl _)
| 0        (succ b) ha hb h := absurd ha (lt_irrefl _)
| 0        0        ha hb h := rfl

/- TODO(Leo): sub + inequalities -/

protected def {u} strong_rec_on {p : nat → Sort u} (n : nat) (h : ∀ n, (∀ m, m < n → p m) → p n) : p n :=
suffices ∀ n m, m < n → p m, from this (succ n) n (lt_succ_self _),
begin
  intros n, induction n with n ih,
    {intros m h₁, exact absurd h₁ (not_lt_zero _)},
    {intros m h₁,
      apply or.by_cases (lt_or_eq_of_le (le_of_lt_succ h₁)),
        {intros, apply ih, assumption},
        {intros, subst m, apply h _ ih}}
end

protected lemma strong_induction_on {p : nat → Prop} (n : nat) (h : ∀ n, (∀ m, m < n → p m) → p n) : p n :=
nat.strong_rec_on n h

protected lemma case_strong_induction_on {p : nat → Prop} (a : nat)
  (hz : p 0)
  (hi : ∀ n, (∀ m, m ≤ n → p m) → p (succ n)) : p a :=
nat.strong_induction_on a $ λ n,
  match n with
  | 0     := λ _, hz
  | (n+1) := λ h₁, hi n (λ m h₂, h₁ _ (lt_succ_of_le h₂))
  end

/- mod -/
lemma mod_def (x y : nat) : mod x y = if 0 < y ∧ y ≤ x then mod (x - y) y else x :=
by note h := mod_def_aux x y; rwa [dif_eq_if] at h

lemma mod_zero (a : nat) : a % 0 = a :=
begin
  rw mod_def,
  assert h : ¬ (0 < 0 ∧ 0 ≤ a),
  simp [lt_irrefl],
  simp [if_neg, h]
end

lemma mod_eq_of_lt {a b : nat} (h : a < b) : a % b = a :=
begin
  rw mod_def,
  assert h' : ¬(0 < b ∧ b ≤ a),
  simp [not_le_of_gt h],
  simp [if_neg, h']
end

lemma zero_mod (b : nat) : 0 % b = 0 :=
begin
  rw mod_def,
  assert h : ¬(0 < b ∧ b ≤ 0),
  {intro hn, cases hn with l r, exact absurd (lt_of_lt_of_le l r) (lt_irrefl 0)},
  simp [if_neg, h]
end

lemma mod_eq_sub_mod {a b : nat} (h₁ : b > 0) (h₂ : a ≥ b) : a % b = (a - b) % b :=
by rw [mod_def, if_pos (and.intro h₁ h₂)]

lemma mod_lt (x : nat) {y : nat} (h : y > 0) : x % y < y :=
begin
  induction x using nat.case_strong_induction_on with x ih,
  {rw zero_mod, assumption},
  {apply or.elim (decidable.em (succ x < y)),
    {intro h₁, rwa [mod_eq_of_lt h₁]},
    {intro h₁,
      assert h₁ : succ x % y = (succ x - y) % y, {exact mod_eq_sub_mod h (le_of_not_gt h₁)},
      assert this : succ x - y ≤ x, {exact le_of_lt_succ (sub_lt (succ_pos x) h)},
      assert h₂ : (succ x - y) % y < y, {exact ih _ this},
      rwa -h₁ at h₂}}
end

lemma eq_zero_of_le_zero : ∀ {n : nat}, n ≤ 0 → n = 0
| 0     h := rfl
| (n+1) h := absurd (zero_lt_succ n) (not_lt_of_ge h)

lemma mod_one (n : ℕ) : n % 1 = 0 :=
have n % 1 < 1, from (mod_lt n) (succ_pos 0),
eq_zero_of_le_zero (le_of_lt_succ this)

lemma mod_two_eq_zero_or_one (n : ℕ)
: n % 2 = 0 ∨ n % 2 = 1 :=
begin
  assert h : ((n % 2 < 1) ∨ (n % 2 = 1)),
  { apply lt_or_eq_of_le,
    apply nat.le_of_succ_le_succ,
    apply @nat.mod_lt n 2 (nat.le_succ _) },
  cases h with h h,
  { left,
    apply nat.le_antisymm ,
    { apply nat.le_of_succ_le_succ h },
    { apply nat.zero_le } },
  { right,
    apply h }
end

lemma cond_to_bool_mod_two (x : ℕ) [d : decidable (x % 2 = 1)]
: cond (@to_bool (x % 2 = 1) d) 1 0 = x % 2 :=
begin
  cases d with h h
  ; unfold decidable.to_bool cond,
  { cases mod_two_eq_zero_or_one x with h' h',
    rw h', cases h h' },
  { rw h },
end

lemma sub_mul_mod (x k n : ℕ)
  (h₀ : 0 < n)
  (h₁ : n*k ≤ x)
: (x - n*k) % n = x % n :=
begin
  induction k with k,
  { simp },
  { assert h₂ : n * k ≤ x,
    { rw [mul_succ] at h₁,
      apply nat.le_trans _ h₁,
      apply le_add_right _ n },
    assert h₄ : x - n * k ≥ n,
    { apply @nat.le_of_add_le_add_right (n*k),
      rw [nat.sub_add_cancel h₂],
      simp [mul_succ] at h₁, simp [h₁] },
    rw [mul_succ,-nat.sub_sub,-mod_eq_sub_mod h₀ h₄,ih_1 h₂] }
end

/- div & mod -/
lemma div_def (x y : nat) : div x y = if 0 < y ∧ y ≤ x then div (x - y) y + 1 else 0 :=
by note h := div_def_aux x y; rwa dif_eq_if at h

lemma mod_add_div (m k : ℕ)
: m % k + k * (m / k) = m :=
begin
  apply nat.strong_induction_on m,
  clear m,
  intros m IH,
  cases decidable.em (0 < k ∧ k ≤ m) with h h',
  -- 0 < k ∧ k ≤ m
  { assert h' : m - k < m,
    { apply nat.sub_lt _ h.left,
      apply lt_of_lt_of_le h.left h.right },
    rw [div_def, mod_def, if_pos h, if_pos h],
    simp [left_distrib,IH _ h'],
    rw [-nat.add_sub_assoc h.right,nat.add_sub_cancel_left] },
  -- ¬ (0 < k ∧ k ≤ m)
  { rw [div_def, mod_def, if_neg h', if_neg h'], simp },
end

/- div -/

protected lemma div_one (n : ℕ) : n / 1 = n :=
have n % 1 + 1 * (n / 1) = n, from mod_add_div _ _,
by simp [mod_one] at this; assumption

protected lemma div_zero (n : ℕ) : n / 0 = 0 :=
begin rw [div_def], simp [lt_irrefl] end

protected lemma div_le_of_le_mul {m n : ℕ} : ∀ {k}, m ≤ k * n → m / k ≤ n
| 0        h := by simp [nat.div_zero]; apply zero_le
| (succ k) h :=
  suffices succ k * (m / succ k) ≤ succ k * n, from le_of_mul_le_mul_left this (zero_lt_succ _),
  calc
    succ k * (m / succ k) ≤ m % succ k + succ k * (m / succ k) : le_add_left _ _
                      ... = m                                  : by rw mod_add_div
                      ... ≤ succ k * n                         : h

protected lemma div_le_self : ∀ (m n : ℕ), m / n ≤ m
| m 0        := by simp [nat.div_zero]; apply zero_le
| m (succ n) :=
  have m ≤ succ n * m, from calc
    m  = 1 * m      : by simp
   ... ≤ succ n * m : mul_le_mul_right _ (succ_le_succ (zero_le _)),
  nat.div_le_of_le_mul this

lemma div_eq_sub_div {a b : nat} (h₁ : b > 0) (h₂ : a ≥ b)
: a / b = (a - b) / b + 1 :=
begin
  rw [div_def a,if_pos],
  split ; assumption
end

lemma sub_mul_div (x n p : ℕ)
  (h₀ : 0 < n)
  (h₁ : n*p ≤ x)
: (x - n*p) / n = x / n - p :=
begin
  induction p with p,
  { simp },
  { assert h₂ : n*p ≤ x,
    { transitivity,
      { apply nat.mul_le_mul_left, apply le_succ },
      { apply h₁ }  },
    assert h₃ : x - n * p ≥ n,
    { apply le_of_add_le_add_right,
      rw [nat.sub_add_cancel h₂,add_comm],
      rw [mul_succ] at h₁,
      apply h₁ },
    rw [sub_succ,-ih_1 h₂],
    rw [@div_eq_sub_div (x - n*p) _ h₀ h₃],
    simp [add_one_eq_succ,pred_succ,mul_succ,nat.sub_sub] }
end

lemma div_eq_of_lt {a b : ℕ} (h₀ : a < b)
: a / b = 0 :=
begin
  rw [div_def a,if_neg],
  intro h₁,
  apply not_le_of_gt h₀ h₁.right
end

-- this is a Galois connection
--   f x ≤ y ↔ x ≤ g y
-- with
--   f x = x * k
--   g y = y / k
theorem le_div_iff_mul_le (x y : ℕ) {k : ℕ}
  (Hk : k > 0)
: x ≤ y / k ↔ x * k ≤ y :=
begin
  -- Hk is needed because, despite div being made total, y / 0 := 0
  --     x * 0 ≤ y ↔ x ≤ y / 0
  --   ↔ 0 ≤ y ↔ x ≤ 0
  --   ↔ true ↔ x = 0
  --   ↔ x = 0
  revert x,
  apply nat.strong_induction_on y _,
  clear y,
  intros y IH x,
  cases lt_or_ge y k with h h,
  -- base case: y < k
  { rw [div_eq_of_lt h],
    cases x with x,
    { simp [zero_mul,zero_le_iff_true] },
    { simp [succ_mul,succ_le_zero_iff_false],
      apply not_le_of_gt,
      apply lt_of_lt_of_le h,
      apply le_add_right } },
  -- step: k ≤ y
  { rw [div_eq_sub_div Hk h],
    cases x with x,
    { simp [zero_mul,zero_le_iff_true] },
    { assert Hlt : y - k < y,
      { apply sub_lt_of_pos_le ; assumption },
      rw [ -add_one_eq_succ
         , nat.add_le_add_iff_le_right
         , IH (y - k) Hlt x
         , succ_mul,add_le_to_le_sub _ h] } }
end

theorem div_lt_iff_lt_mul (x y : ℕ) {k : ℕ}
  (Hk : k > 0)
: x / k < y ↔ x < y * k :=
begin
  simp [lt_iff_not_ge],
  apply not_iff_not_of_iff,
  apply le_div_iff_mul_le _ _ Hk
end

/- pow -/

lemma pos_pow_of_pos {b : ℕ} : ∀ (n : ℕ) (h : 0 < b), 0 < b^n
  | 0 _ := nat.le_refl _
  | (succ n) h :=
begin
  rw -mul_zero 0,
  apply mul_lt_mul (pos_pow_of_pos _ h) h,
  apply nat.le_refl,
  apply zero_le
end

/- mod / div / pow -/

theorem mod_pow_succ {b : ℕ} (b_pos : b > 0) (w m : ℕ)
: m % (b^succ w) = b * (m/b % b^w) + m % b :=
begin
  apply nat.strong_induction_on m,
  clear m,
  intros p IH,
  cases lt_or_ge p (b^succ w) with h₁ h₁,
  -- base case: p < b^succ w
  { assert h₂ : p / b < b^w,
    { apply (div_lt_iff_lt_mul p _ b_pos).mpr,
      simp at h₁, simp [h₁] },
    rw [mod_eq_of_lt h₁,mod_eq_of_lt h₂], simp [mod_add_div], },
  -- step: p ≥ b^succ w
  { assert h₄ : ∀ {x}, b^x > 0,
    { intro x, apply pos_pow_of_pos _ b_pos },
    assert h₂ : p - b^succ w < p,
    { apply sub_lt_of_pos_le _ _ h₄ h₁ },
    assert h₅ : b * b^w ≤ p,
    { simp at h₁, simp [h₁] },
    rw [mod_eq_sub_mod h₄ h₁,IH _ h₂,pow_succ],
    apply congr, apply congr_arg,
    { assert h₃ : p / b ≥ b^w,
      { apply (le_div_iff_mul_le _ p b_pos).mpr, simp [h₅] },
      simp [nat.sub_mul_div _ _ _ b_pos h₅,mod_eq_sub_mod h₄ h₃] },
    { simp [nat.sub_mul_mod p (b^w) _ b_pos h₅] } }
end

end nat
