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

lemma add_succ (n m : ℕ) : n + succ m = succ (n + m) :=
rfl

protected lemma add_zero (n : ℕ) : n + 0 = n :=
rfl

lemma add_one (n : ℕ) : n + 1 = succ n :=
rfl

lemma succ_eq_add_one (n : ℕ) : succ n = n + 1 :=
rfl

protected lemma add_comm : ∀ n m : ℕ, n + m = m + n
| n 0     := eq.symm (nat.zero_add n)
| n (m+1) :=
  suffices succ (n + m) = succ (m + n), from
    eq.symm (succ_add m n) ▸ this,
  congr_arg succ (add_comm n m)

protected lemma add_assoc : ∀ n m k : ℕ, (n + m) + k = n + (m + k)
| n m 0        := rfl
| n m (succ k) := by rw [add_succ, add_succ, add_assoc]

protected lemma add_left_comm : ∀ (n m k : ℕ), n + (m + k) = m + (n + k) :=
left_comm nat.add nat.add_comm nat.add_assoc

protected lemma add_left_cancel : ∀ {n m k : ℕ}, n + m = n + k → m = k
| 0        m k := by simp [nat.zero_add] {contextual := tt}
| (succ n) m k := λ h,
  have n+m = n+k, by simp [succ_add] at h; injection h,
  add_left_cancel this

protected lemma add_right_cancel {n m k : ℕ} (h : n + m = k + m) : n = k :=
have m + n = m + k, by rwa [nat.add_comm n m, nat.add_comm k m] at h,
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
    rw [add_one, succ_add] at h,
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

protected lemma mul_one : ∀ (n : ℕ), n * 1 = n := nat.zero_add

protected lemma one_mul (n : ℕ) : 1 * n = n :=
by rw [nat.mul_comm, nat.mul_one]

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

lemma le_succ_of_le {n m : ℕ} (h : n ≤ m) : n ≤ succ m :=
nat.le_trans h (le_succ m)

lemma le_of_succ_le {n m : ℕ} (h : succ n ≤ m) : n ≤ m :=
nat.le_trans (le_succ n) h

protected lemma le_of_lt {n m : ℕ} (h : n < m) : n ≤ m :=
le_of_succ_le h

def lt.step {n m : ℕ} : n < m → n < succ m := less_than_or_equal.step

lemma eq_zero_or_pos (n : ℕ) : n = 0 ∨ n > 0 :=
by {cases n, exact or.inl rfl, exact or.inr (succ_pos _)}

protected lemma pos_of_ne_zero {n : nat} : n ≠ 0 → n > 0 :=
or.resolve_left (eq_zero_or_pos n)

protected lemma lt_trans {n m k : ℕ} (h₁ : n < m) : m < k → n < k :=
nat.le_trans (less_than_or_equal.step h₁)

protected lemma lt_of_le_of_lt {n m k : ℕ} (h₁ : n ≤ m) : m < k → n < k :=
nat.le_trans (succ_le_succ h₁)

def lt.base (n : ℕ) : n < succ n := nat.le_refl (succ n)

lemma lt_succ_self (n : ℕ) : n < succ n := lt.base n

protected lemma le_antisymm {n m : ℕ} (h₁ : n ≤ m) : m ≤ n → n = m :=
less_than_or_equal.cases_on h₁ (λ a, rfl) (λ a b c, absurd (nat.lt_of_le_of_lt b c) (nat.lt_irrefl n))

instance : weak_order ℕ :=
⟨@nat.less_than_or_equal, @nat.le_refl, @nat.le_trans, @nat.le_antisymm⟩

lemma eq_zero_of_le_zero {n : nat} (h : n ≤ 0) : n = 0 :=
le_antisymm h (zero_le _)

protected lemma le_of_eq_or_lt {a b : ℕ} (h : a = b ∨ a < b) : a ≤ b :=
or.elim h nat.le_of_eq nat.le_of_lt

lemma succ_lt_succ {a b : ℕ} : a < b → succ a < succ b :=
succ_le_succ

lemma lt_of_succ_lt {a b : ℕ} : succ a < b → a < b :=
le_of_succ_le

lemma lt_of_succ_lt_succ {a b : ℕ} : succ a < succ b → a < b :=
le_of_succ_le_succ

lemma pred_lt_pred : ∀ {n m : ℕ}, n ≠ 0 → m ≠ 0 → n < m → pred n < pred m
| 0         _       h₁ h₂ h := absurd rfl h₁
| _         0       h₁ h₂ h := absurd rfl h₂
| (succ n) (succ m) _  _  h := lt_of_succ_lt_succ h

protected lemma lt_or_ge : ∀ (a b : ℕ), a < b ∨ a ≥ b
| a 0     := or.inr (zero_le a)
| a (b+1) :=
  match lt_or_ge a b with
  | or.inl h := or.inl (le_succ_of_le h)
  | or.inr h :=
    match nat.eq_or_lt_of_le h with
    | or.inl h1 := or.inl (h1 ▸ lt_succ_self b)
    | or.inr h1 := or.inr h1
    end
  end

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
  rw [nat.add_comm _ k, nat.add_comm _ k],
  apply nat.le_of_add_le_add_left
end

protected lemma add_le_add_iff_le_right (k n m : ℕ) : n + k ≤ m + k ↔ n ≤ m :=
  ⟨ nat.le_of_add_le_add_right , assume h, nat.add_le_add_right h _ ⟩

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

protected lemma lt_add_of_pos_left {n k : ℕ} (h : k > 0) : n < k + n :=
by rw add_comm; exact nat.lt_add_of_pos_right h

protected lemma zero_lt_one : 0 < (1:nat) :=
zero_lt_succ 0

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
  have k * n + k * l = k * m, by rw [← left_distrib, hl],
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
  mul_le_mul_of_nonneg_left  := assume a b c h₁ h₂, nat.mul_le_mul_left c h₁,
  mul_le_mul_of_nonneg_right := assume a b c h₁ h₂, nat.mul_le_mul_right c h₁,
  mul_lt_mul_of_pos_left     := @nat.mul_lt_mul_of_pos_left,
  mul_lt_mul_of_pos_right    := @nat.mul_lt_mul_of_pos_right,
  decidable_lt               := nat.decidable_lt,
  decidable_le               := nat.decidable_le,
  decidable_eq               := nat.decidable_eq }

-- all the fields are already included in the decidable_linear_ordered_semiring instance
instance : decidable_linear_ordered_cancel_comm_monoid ℕ :=
{ nat.decidable_linear_ordered_semiring with
  add_left_cancel := @nat.add_left_cancel }

lemma le_of_lt_succ {m n : nat} : m < succ n → m ≤ n :=
le_of_succ_le_succ

theorem eq_of_mul_eq_mul_left {m k n : ℕ} (Hn : n > 0) (H : n * m = n * k) : m = k :=
le_antisymm (le_of_mul_le_mul_left (le_of_eq H) Hn)
            (le_of_mul_le_mul_left (le_of_eq H.symm) Hn)

theorem eq_of_mul_eq_mul_right {n m k : ℕ} (Hm : m > 0) (H : n * m = k * m) : n = k :=
by rw [mul_comm n m, mul_comm k m] at H; exact eq_of_mul_eq_mul_left Hm H

/- sub properties -/

@[simp] protected lemma zero_sub : ∀ a : ℕ, 0 - a = 0
| 0     := rfl
| (a+1) := congr_arg pred (zero_sub a)

lemma sub_lt_succ (a b : ℕ) : a - b < succ a :=
lt_succ_of_le (sub_le a b)

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
  begin unfold bit0 at h, simp [add_one, add_succ, succ_add] at h, exact h end,
  have n + n = m + m, by repeat {injection this with this},
  have n = m, from bit0_inj this,
  by rw this

protected lemma bit1_inj : ∀ {n m : ℕ}, bit1 n = bit1 m → n = m :=
λ n m h,
have succ (bit0 n) = succ (bit0 m), begin simp [nat.bit1_eq_succ_bit0] at h, assumption end,
have bit0 n = bit0 m, by injection this,
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
by rw [← nat.add_sub_cancel x k, nat.sub_le_sub_right_iff _ _ _ h, nat.add_sub_cancel]

lemma sub_lt_of_pos_le (a b : ℕ) (h₀ : 0 < a) (h₁ : a ≤ b)
: b - a < b :=
begin
  apply sub_lt _ h₀,
  apply lt_of_lt_of_le h₀ h₁
end

theorem sub_one (n : ℕ) : n - 1 = pred n :=
rfl

theorem succ_sub_one (n : ℕ) : succ n - 1 = n :=
rfl

theorem succ_pred_eq_of_pos : ∀ {n : ℕ}, n > 0 → succ (pred n) = n
| 0 h        := absurd h (lt_irrefl 0)
| (succ k) h := rfl

theorem sub_eq_zero_of_le {n m : ℕ} (h : n ≤ m) : n - m = 0 :=
exists.elim (nat.le.dest h)
  (assume k, assume hk : n + k = m, by rw [← hk, sub_self_add])

protected theorem le_of_sub_eq_zero : ∀{n m : ℕ}, n - m = 0 → n ≤ m
| n 0 H := begin rw [nat.sub_zero] at H, simp [H] end
| 0 (m+1) H := zero_le _
| (n+1) (m+1) H := add_le_add_right
  (le_of_sub_eq_zero begin simp [nat.add_sub_add_right] at H, exact H end) _

protected theorem sub_eq_zero_iff_le {n m : ℕ} : n - m = 0 ↔ n ≤ m :=
⟨nat.le_of_sub_eq_zero, nat.sub_eq_zero_of_le⟩

theorem add_sub_of_le {n m : ℕ} (h : n ≤ m) : n + (m - n) = m :=
exists.elim (nat.le.dest h)
  (assume k, assume hk : n + k = m,
    by rw [← hk, nat.add_sub_cancel_left])

protected theorem sub_add_cancel {n m : ℕ} (h : n ≥ m) : n - m + m = n :=
by rw [add_comm, add_sub_of_le h]

protected theorem add_sub_assoc {m k : ℕ} (h : k ≤ m) (n : ℕ) : n + m - k = n + (m - k) :=
exists.elim (nat.le.dest h)
  (assume l, assume hl : k + l = m,
    by rw [← hl, nat.add_sub_cancel_left, add_comm k, ← add_assoc, nat.add_sub_cancel])

protected lemma sub_eq_iff_eq_add {a b c : ℕ} (ab : b ≤ a) : a - b = c ↔ a = c + b :=
⟨assume c_eq, begin rw [c_eq.symm, nat.sub_add_cancel ab] end,
  assume a_eq, begin rw [a_eq, nat.add_sub_cancel] end⟩

protected lemma lt_of_sub_eq_succ {m n l : ℕ} (H : m - n = nat.succ l) : n < m :=
lt_of_not_ge
  (assume (H' : n ≥ m), begin simp [nat.sub_eq_zero_of_le H'] at H, contradiction end)

@[simp] lemma zero_min (a : ℕ) : min 0 a = 0 :=
min_eq_left (zero_le a)

@[simp] lemma min_zero (a : ℕ) : min a 0 = 0 :=
min_eq_right (zero_le a)

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
lemma mod_def (x y : nat) : x % y = if 0 < y ∧ y ≤ x then (x - y) % y else x :=
by have h := mod_def_aux x y; rwa [dif_eq_if] at h

@[simp] lemma mod_zero (a : nat) : a % 0 = a :=
begin
  rw mod_def,
  have h : ¬ (0 < 0 ∧ 0 ≤ a),
  simp [lt_irrefl],
  simp [if_neg, h]
end

lemma mod_eq_of_lt {a b : nat} (h : a < b) : a % b = a :=
begin
  rw mod_def,
  have h' : ¬(0 < b ∧ b ≤ a),
  simp [not_le_of_gt h],
  simp [if_neg, h']
end

@[simp] lemma zero_mod (b : nat) : 0 % b = 0 :=
begin
  rw mod_def,
  have h : ¬(0 < b ∧ b ≤ 0),
  {intro hn, cases hn with l r, exact absurd (lt_of_lt_of_le l r) (lt_irrefl 0)},
  simp [if_neg, h]
end

lemma mod_eq_sub_mod {a b : nat} (h : a ≥ b) : a % b = (a - b) % b :=
or.elim (eq_zero_or_pos b)
  (λb0, by rw [b0, nat.sub_zero])
  (λh₂, by rw [mod_def, if_pos (and.intro h₂ h)])

lemma mod_lt (x : nat) {y : nat} (h : y > 0) : x % y < y :=
begin
  induction x using nat.case_strong_induction_on with x ih,
  {rw zero_mod, assumption},
  {apply or.elim (decidable.em (succ x < y)),
    {intro h₁, rwa [mod_eq_of_lt h₁]},
    {intro h₁,
      have h₁ : succ x % y = (succ x - y) % y, {exact mod_eq_sub_mod (le_of_not_gt h₁)},
      have this : succ x - y ≤ x, {exact le_of_lt_succ (sub_lt (succ_pos x) h)},
      have h₂ : (succ x - y) % y < y, {exact ih _ this},
      rwa [← h₁] at h₂}}
end

@[simp] theorem mod_self (n : nat) : n % n = 0 :=
by rw [mod_eq_sub_mod (le_refl _), nat.sub_self, zero_mod]

@[simp] lemma mod_one (n : ℕ) : n % 1 = 0 :=
have n % 1 < 1, from (mod_lt n) (succ_pos 0),
eq_zero_of_le_zero (le_of_lt_succ this)

lemma mod_two_eq_zero_or_one (n : ℕ) : n % 2 = 0 ∨ n % 2 = 1 :=
match n % 2, @nat.mod_lt n 2 dec_trivial with
| 0,   _ := or.inl rfl
| 1,   _ := or.inr rfl
| k+2, h := absurd h dec_trivial
end

/- div & mod -/
lemma div_def (x y : nat) : x / y = if 0 < y ∧ y ≤ x then (x - y) / y + 1 else 0 :=
by have h := div_def_aux x y; rwa dif_eq_if at h

lemma mod_add_div (m k : ℕ)
: m % k + k * (m / k) = m :=
begin
  apply nat.strong_induction_on m,
  clear m,
  intros m IH,
  cases decidable.em (0 < k ∧ k ≤ m) with h h',
  -- 0 < k ∧ k ≤ m
  { have h' : m - k < m,
    { apply nat.sub_lt _ h.left,
      apply lt_of_lt_of_le h.left h.right },
    rw [div_def, mod_def, if_pos h, if_pos h],
    simp [left_distrib, IH _ h'],
    rw [← nat.add_sub_assoc h.right, nat.add_sub_cancel_left] },
  -- ¬ (0 < k ∧ k ≤ m)
  { rw [div_def, mod_def, if_neg h', if_neg h'], simp },
end

/- div -/

protected lemma div_one (n : ℕ) : n / 1 = n :=
have n % 1 + 1 * (n / 1) = n, from mod_add_div _ _,
by simp [mod_one] at this; assumption

protected lemma div_zero (n : ℕ) : n / 0 = 0 :=
begin rw [div_def], simp [lt_irrefl] end

@[simp] protected lemma zero_div (b : ℕ) : 0 / b = 0 :=
eq.trans (div_def 0 b) $ if_neg (and.rec not_le_of_gt)

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

lemma div_eq_sub_div {a b : nat} (h₁ : b > 0) (h₂ : a ≥ b) : a / b = (a - b) / b + 1 :=
begin
  rw [div_def a, if_pos],
  split ; assumption
end

lemma div_eq_of_lt {a b : ℕ} (h₀ : a < b) : a / b = 0 :=
begin
  rw [div_def a, if_neg],
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
    { simp [zero_mul, zero_le] },
    { simp [succ_mul, not_succ_le_zero],
      apply not_le_of_gt,
      apply lt_of_lt_of_le h,
      apply le_add_right } },
  -- step: k ≤ y
  { rw [div_eq_sub_div Hk h],
    cases x with x,
    { simp [zero_mul, zero_le] },
    { have Hlt : y - k < y,
      { apply sub_lt_of_pos_le ; assumption },
      rw [ ← add_one
         , nat.add_le_add_iff_le_right
         , IH (y - k) Hlt x
         , add_one
         , succ_mul, add_le_to_le_sub _ h ]
     } }
end

theorem div_lt_iff_lt_mul (x y : ℕ) {k : ℕ}
  (Hk : k > 0)
: x / k < y ↔ x < y * k :=
begin
  simp [lt_iff_not_ge],
  apply not_iff_not_of_iff,
  apply le_div_iff_mul_le _ _ Hk
end

end nat
