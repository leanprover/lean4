/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura
-/
prelude
import init.core

notation `ℕ` := nat

namespace nat

inductive less_than_or_equal (a : ℕ) : ℕ → Prop
| refl : less_than_or_equal a
| step : Π {b}, less_than_or_equal b → less_than_or_equal (succ b)

instance : has_le ℕ :=
⟨nat.less_than_or_equal⟩

@[reducible] protected def le (n m : ℕ) := nat.less_than_or_equal n m
@[reducible] protected def lt (n m : ℕ) := nat.less_than_or_equal (succ n) m

instance : has_lt ℕ :=
⟨nat.lt⟩

def pred : ℕ → ℕ
| 0     := 0
| (a+1) := a

protected def sub : ℕ → ℕ → ℕ
| a 0     := a
| a (b+1) := pred (sub a b)

protected def mul : nat → nat → nat
| a 0     := 0
| a (b+1) := (mul a b) + a

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

def {u} repeat {α : Type u} (f : ℕ → α → α) : ℕ → α → α
| 0         a := a
| (succ n)  a := f n (repeat n a)

instance : inhabited ℕ :=
⟨nat.zero⟩

protected def pow (b : ℕ) : ℕ → ℕ
| 0        := 1
| (succ n) := pow n * b

instance : has_pow nat nat :=
⟨nat.pow⟩

/- nat.add theorems -/

protected theorem zero_add : ∀ n : ℕ, 0 + n = n
| 0     := rfl
| (n+1) := congr_arg succ (zero_add n)

theorem succ_add : ∀ n m : ℕ, (succ n) + m = succ (n + m)
| n 0     := rfl
| n (m+1) := congr_arg succ (succ_add n m)

theorem add_succ (n m : ℕ) : n + succ m = succ (n + m) :=
rfl

protected theorem add_zero (n : ℕ) : n + 0 = n :=
rfl

theorem add_one (n : ℕ) : n + 1 = succ n :=
rfl

theorem succ_eq_add_one (n : ℕ) : succ n = n + 1 :=
rfl

protected theorem add_comm : ∀ n m : ℕ, n + m = m + n
| n 0     := eq.symm (nat.zero_add n)
| n (m+1) :=
  suffices succ (n + m) = succ (m + n), from
    eq.symm (succ_add m n) ▸ this,
  congr_arg succ (add_comm n m)

protected theorem add_assoc : ∀ n m k : ℕ, (n + m) + k = n + (m + k)
| n m 0        := rfl
| n m (succ k) := congr_arg succ (add_assoc n m k)

protected theorem add_left_comm : ∀ (n m k : ℕ), n + (m + k) = m + (n + k) :=
left_comm nat.add nat.add_comm nat.add_assoc

protected theorem add_right_comm : ∀ (n m k : ℕ), (n + m) + k = (n + k) + m :=
right_comm nat.add nat.add_comm nat.add_assoc

protected theorem add_left_cancel : ∀ {n m k : ℕ}, n + m = n + k → m = k
| 0        m k h := nat.zero_add m ▸ nat.zero_add k ▸ h
| (succ n) m k h :=
  have n+m = n+k, from
    have succ (n + m) = succ (n + k), from succ_add n m ▸ succ_add n k ▸ h,
    nat.no_confusion this id,
  add_left_cancel this

protected theorem add_right_cancel {n m k : ℕ} (h : n + m = k + m) : n = k :=
have m + n = m + k, from nat.add_comm n m ▸ nat.add_comm k m ▸ h,
nat.add_left_cancel this

/- nat.mul theorems -/

protected theorem mul_zero (n : ℕ) : n * 0 = 0 :=
rfl

theorem mul_succ (n m : ℕ) : n * succ m = n * m + n :=
rfl

protected theorem zero_mul : ∀ (n : ℕ), 0 * n = 0
| 0        := rfl
| (succ n) := (mul_succ 0 n).symm ▸ (zero_mul n).symm ▸ rfl

theorem succ_mul : ∀ (n m : ℕ), (succ n) * m = (n * m) + m
| n 0        := rfl
| n (succ m) :=
  have succ (n * m + m + n) = succ (n * m + n + m), from
    congr_arg succ (nat.add_right_comm _ _ _),
  (mul_succ n m).symm ▸ (mul_succ (succ n) m).symm ▸ (succ_mul n m).symm ▸ this

protected theorem mul_comm : ∀ (n m : ℕ), n * m = m * n
| n 0        := (nat.zero_mul n).symm ▸ (nat.mul_zero n).symm ▸ rfl
| n (succ m) := (mul_succ n m).symm ▸ (succ_mul m n).symm ▸ (mul_comm n m).symm ▸ rfl

protected theorem mul_one : ∀ (n : ℕ), n * 1 = n :=
nat.zero_add

protected theorem one_mul (n : ℕ) : 1 * n = n :=
nat.mul_comm n 1 ▸ nat.mul_one n

protected theorem left_distrib : ∀ (n m k : ℕ), n * (m + k) = n * m + n * k
| 0        m k := (nat.zero_mul (m + k)).symm ▸ (nat.zero_mul m).symm ▸ (nat.zero_mul k).symm ▸ rfl
| (succ n) m k := calc
  succ n * (m + k)
        = n * (m + k) + (m + k)      : succ_mul _ _
    ... = (n * m + n * k) + (m + k)  : left_distrib n m k ▸ rfl
    ... = n * m + (n * k + (m + k))  : nat.add_assoc _ _ _
    ... = n * m + (m + (n * k + k))  : congr_arg (λ x, n*m + x) (nat.add_left_comm _ _ _)
    ... = (n * m + m) + (n * k + k)  : (nat.add_assoc _ _ _).symm
    ... = (n * m + m) + succ n * k   : succ_mul n k ▸ rfl
    ... = succ n * m + succ n * k    : succ_mul n m ▸ rfl

protected theorem right_distrib (n m k : ℕ) : (n + m) * k = n * k + m * k :=
calc (n + m) * k
       = k * (n + m)   : nat.mul_comm _ _
  ...  = k * n + k * m : nat.left_distrib _ _ _
  ...  = n * k + k * m : nat.mul_comm n k ▸ rfl
  ...  = n * k + m * k : nat.mul_comm m k ▸ rfl

protected theorem mul_assoc : ∀ (n m k : ℕ), (n * m) * k = n * (m * k)
| n m 0        := rfl
| n m (succ k) := calc
  n * m * succ k
       = n * m * (k + 1)           : rfl
   ... = (n * m * k) + n * m * 1   : nat.left_distrib _ _ _
   ... = (n * m * k) + n * m       : (nat.mul_one (n*m)).symm ▸ rfl
   ... = (n * (m * k)) + n * m     : (mul_assoc n m k).symm ▸ rfl
   ... = n * (m * k + m)           : (nat.left_distrib n (m*k) m).symm
   ... = n * (m * succ k)          : nat.mul_succ m k ▸ rfl

/- Inequalities -/

@[refl] protected def le_refl : ∀ a : ℕ, a ≤ a :=
less_than_or_equal.refl

theorem le_succ (n : ℕ) : n ≤ succ n :=
less_than_or_equal.step (nat.le_refl n)

theorem succ_le_succ {n m : ℕ} : n ≤ m → succ n ≤ succ m :=
λ h, less_than_or_equal.rec (nat.le_refl (succ n)) (λ a b, less_than_or_equal.step) h

theorem succ_lt_succ {a b : ℕ} : a < b → succ a < succ b :=
succ_le_succ

theorem zero_le : ∀ (n : ℕ), 0 ≤ n
| 0     := nat.le_refl 0
| (n+1) := less_than_or_equal.step (zero_le n)

theorem zero_lt_succ (n : ℕ) : 0 < succ n :=
succ_le_succ (zero_le n)

def succ_pos := zero_lt_succ

theorem not_succ_le_zero : ∀ (n : ℕ), succ n ≤ 0 → false
.

theorem not_lt_zero (a : ℕ) : ¬ a < 0 := not_succ_le_zero a

theorem pred_le_pred {n m : ℕ} : n ≤ m → pred n ≤ pred m :=
λ h, less_than_or_equal.rec_on h
  (nat.le_refl (pred n))
  (λ n, nat.rec (λ a b, b) (λ a b c, less_than_or_equal.step) n)

theorem le_of_succ_le_succ {n m : ℕ} : succ n ≤ succ m → n ≤ m :=
pred_le_pred

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

protected theorem eq_or_lt_of_le {a b : ℕ} (h : a ≤ b) : a = b ∨ a < b :=
less_than_or_equal.cases_on h (or.inl rfl) (λ n h, or.inr (succ_le_succ h))

theorem lt_succ_of_le {a b : ℕ} : a ≤ b → a < succ b :=
succ_le_succ

protected theorem sub_zero (n : ℕ) : n - 0 = n :=
rfl

theorem succ_sub_succ_eq_sub (a b : ℕ) : succ a - succ b = a - b :=
nat.rec_on b
  (show succ a - succ zero = a - zero, from (eq.refl (succ a - succ zero)))
  (λ b, congr_arg pred)

theorem not_succ_le_self : ∀ n : ℕ, ¬succ n ≤ n :=
λ n, nat.rec (not_succ_le_zero 0) (λ a b c, b (le_of_succ_le_succ c)) n

protected theorem lt_irrefl (n : ℕ) : ¬n < n :=
not_succ_le_self n

protected theorem le_trans {n m k : ℕ} (h1 : n ≤ m) : m ≤ k → n ≤ k :=
less_than_or_equal.rec h1 (λ p h2, less_than_or_equal.step)

theorem pred_le : ∀ (n : ℕ), pred n ≤ n
| 0        := less_than_or_equal.refl 0
| (succ a) := less_than_or_equal.step (less_than_or_equal.refl a)

theorem pred_lt : ∀ {n : ℕ}, n ≠ 0 → pred n < n
| 0        h := absurd rfl h
| (succ a) h := lt_succ_of_le (less_than_or_equal.refl _)

theorem sub_le (a b : ℕ) : a - b ≤ a :=
nat.rec_on b (nat.le_refl (a - 0)) (λ b₁, nat.le_trans (pred_le (a - b₁)))

theorem sub_lt : ∀ {a b : ℕ}, 0 < a → 0 < b → a - b < a
| 0     b     h1 h2 := absurd h1 (nat.lt_irrefl 0)
| (a+1) 0     h1 h2 := absurd h2 (nat.lt_irrefl 0)
| (a+1) (b+1) h1 h2 :=
  eq.symm (succ_sub_succ_eq_sub a b) ▸
    show a - b < succ a, from
    lt_succ_of_le (sub_le a b)

protected theorem lt_of_lt_of_le {n m k : ℕ} : n < m → m ≤ k → n < k :=
nat.le_trans

protected theorem le_of_eq {n m : ℕ} (p : n = m) : n ≤ m :=
p ▸ less_than_or_equal.refl n

theorem le_succ_of_le {n m : ℕ} (h : n ≤ m) : n ≤ succ m :=
nat.le_trans h (le_succ m)

theorem le_of_succ_le {n m : ℕ} (h : succ n ≤ m) : n ≤ m :=
nat.le_trans (le_succ n) h

protected theorem le_of_lt {n m : ℕ} (h : n < m) : n ≤ m :=
le_of_succ_le h

def lt.step {n m : ℕ} : n < m → n < succ m := less_than_or_equal.step

theorem eq_zero_or_pos : ∀ (n : ℕ), n = 0 ∨ n > 0
| 0     := or.inl rfl
| (n+1) := or.inr (succ_pos _)

protected theorem lt_trans {n m k : ℕ} (h₁ : n < m) : m < k → n < k :=
nat.le_trans (less_than_or_equal.step h₁)

protected theorem lt_of_le_of_lt {n m k : ℕ} (h₁ : n ≤ m) : m < k → n < k :=
nat.le_trans (succ_le_succ h₁)

def lt.base (n : ℕ) : n < succ n := nat.le_refl (succ n)

theorem lt_succ_self (n : ℕ) : n < succ n := lt.base n

protected theorem le_antisymm {n m : ℕ} (h₁ : n ≤ m) : m ≤ n → n = m :=
less_than_or_equal.cases_on h₁ (λ a, rfl) (λ a b c, absurd (nat.lt_of_le_of_lt b c) (nat.lt_irrefl n))

protected theorem lt_or_ge : ∀ (a b : ℕ), a < b ∨ a ≥ b
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

protected theorem le_total (m n : ℕ) : m ≤ n ∨ n ≤ m :=
or.elim (nat.lt_or_ge m n)
  (λ h, or.inl (nat.le_of_lt h))
  or.inr

protected theorem lt_of_le_and_ne {m n : ℕ} (h1 : m ≤ n) : m ≠ n → m < n :=
resolve_right (or.swap (nat.eq_or_lt_of_le h1))

theorem eq_zero_of_le_zero {n : nat} (h : n ≤ 0) : n = 0 :=
nat.le_antisymm h (zero_le _)

theorem lt_of_succ_lt {a b : ℕ} : succ a < b → a < b :=
le_of_succ_le

theorem lt_of_succ_lt_succ {a b : ℕ} : succ a < succ b → a < b :=
le_of_succ_le_succ

theorem lt_of_succ_le {a b : ℕ} (h : succ a ≤ b) : a < b := h

theorem succ_le_of_lt {a b : ℕ} (h : a < b) : succ a ≤ b := h

theorem le_add_right : ∀ (n k : ℕ), n ≤ n + k
| n 0     := nat.le_refl n
| n (k+1) := le_succ_of_le (le_add_right n k)

theorem le_add_left (n m : ℕ): n ≤ m + n :=
nat.add_comm n m ▸ le_add_right n m

theorem le.dest : ∀ {n m : ℕ}, n ≤ m → ∃ k, n + k = m
| n ._ (less_than_or_equal.refl ._)  := ⟨0, rfl⟩
| n ._ (@less_than_or_equal.step ._ m h) :=
  match le.dest h with
  | ⟨w, hw⟩ := ⟨succ w, hw ▸ add_succ n w⟩
  end

theorem le.intro {n m k : ℕ} (h : n + k = m) : n ≤ m :=
h ▸ le_add_right n k

protected theorem not_le_of_gt {a b : nat} (h : a > b) : ¬ a ≤ b :=
λ (h₁ : a ≤ b),
  or.elim (nat.lt_or_ge a b)
  (λ h₂, absurd (nat.lt_trans h h₂) (nat.lt_irrefl _))
  (λ h₂, have heq : a = b, from nat.le_antisymm h₁ h₂, absurd (@eq.subst _ _ _ _ heq h) (nat.lt_irrefl b))

theorem gt_of_not_le {a b : nat} (h : ¬ a ≤ b) : a > b :=
or.elim (nat.lt_or_ge b a)
  (λ h₁, h₁)
  (λ h₁, absurd h₁ h)

protected theorem lt_of_le_of_ne {a b : nat} (h₁ : a ≤ b) (h₂ : a ≠ b) : a < b :=
or.elim (nat.lt_or_ge a b)
  (λ h₃, h₃)
  (λ h₃, absurd (nat.le_antisymm h₁ h₃) h₂)

protected theorem add_le_add_left {n m : ℕ} (h : n ≤ m) (k : ℕ) : k + n ≤ k + m :=
match le.dest h with
| ⟨w, hw⟩ :=
  have k + n + w = k + m, from
    calc k + n + w = k + (n + w) : nat.add_assoc _ _ _
            ...    = k + m       : congr_arg _ hw,
  le.intro this
end

protected theorem add_le_add_right {n m : ℕ} (h : n ≤ m) (k : ℕ) : n + k ≤ m + k :=
calc
  n + k = k + n : nat.add_comm _ _
    ... ≤ k + m : nat.add_le_add_left h k
    ... = m + k : nat.add_comm _ _

protected theorem add_lt_add_left {n m : ℕ} (h : n < m) (k : ℕ) : k + n < k + m :=
lt_of_succ_le (add_succ k n ▸ nat.add_le_add_left (succ_le_of_lt h) k)

protected theorem add_lt_add_right {n m : ℕ} (h : n < m) (k : ℕ) : n + k < m + k :=
nat.add_comm k m ▸ nat.add_comm k n ▸ nat.add_lt_add_left h k

protected theorem zero_lt_one : 0 < (1:nat) :=
zero_lt_succ 0

theorem le_of_lt_succ {m n : nat} : m < succ n → m ≤ n :=
le_of_succ_le_succ

lemma add_le_add {a b c d : nat} (h₁ : a ≤ b) (h₂ : c ≤ d) : a + c ≤ b + d :=
nat.le_trans (nat.add_le_add_right h₁ c) (nat.add_le_add_left h₂ b)

lemma add_lt_add {a b c d : nat} (h₁ : a < b) (h₂ : c < d) : a + c < b + d :=
nat.lt_trans (nat.add_lt_add_right h₁ c) (nat.add_lt_add_left h₂ b)

/- Basic theorems for comparing numerals -/

theorem nat_zero_eq_zero : nat.zero = 0 :=
rfl

protected theorem one_ne_zero : 1 ≠ (0 : ℕ) :=
assume h, nat.no_confusion h

protected theorem zero_ne_one : 0 ≠ (1 : ℕ) :=
assume h, nat.no_confusion h

theorem succ_ne_zero (n : ℕ) : succ n ≠ 0 :=
assume h, nat.no_confusion h

protected theorem bit0_succ_eq (n : ℕ) : bit0 (succ n) = succ (succ (bit0 n)) :=
show succ (succ n + n) = succ (succ (n + n)), from
congr_arg succ (succ_add n n)

protected theorem zero_lt_bit0 : ∀ {n : nat}, n ≠ 0 → 0 < bit0 n
| 0        h := absurd rfl h
| (succ n) h :=
  calc 0 < succ (succ (bit0 n)) : zero_lt_succ _
     ... = bit0 (succ n)        : (nat.bit0_succ_eq n).symm

protected theorem zero_lt_bit1 (n : nat) : 0 < bit1 n :=
zero_lt_succ _

protected theorem bit0_ne_zero : ∀ {n : ℕ}, n ≠ 0 → bit0 n ≠ 0
| 0     h := absurd rfl h
| (n+1) h :=
  suffices (n+1) + (n+1) ≠ 0, from this,
  suffices succ ((n+1) + n) ≠ 0, from this,
  λ h, nat.no_confusion h

protected theorem bit1_ne_zero (n : ℕ) : bit1 n ≠ 0 :=
show succ (n + n) ≠ 0, from
λ h, nat.no_confusion h

protected theorem bit1_eq_succ_bit0 (n : ℕ) : bit1 n = succ (bit0 n) :=
rfl

protected theorem bit1_succ_eq (n : ℕ) : bit1 (succ n) = succ (succ (bit1 n)) :=
eq.trans (nat.bit1_eq_succ_bit0 (succ n)) (congr_arg succ (nat.bit0_succ_eq n))

protected theorem bit1_ne_one : ∀ {n : ℕ}, n ≠ 0 → bit1 n ≠ 1
| 0     h h1 := absurd rfl h
| (n+1) h h1 := nat.no_confusion h1 (λ h2, absurd h2 (succ_ne_zero _))

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

protected theorem bit0_ne_bit1 : ∀ (n m : ℕ), bit0 n ≠ bit1 m :=
λ n m : nat, ne.symm (nat.bit1_ne_bit0 m n)

protected theorem bit0_inj : ∀ {n m : ℕ}, bit0 n = bit0 m → n = m
| 0     0     h := rfl
| 0     (m+1) h := absurd h.symm (succ_ne_zero _)
| (n+1) 0     h := absurd h (succ_ne_zero _)
| (n+1) (m+1) h :=
  have (n+1) + n = (m+1) + m, from nat.no_confusion h id,
  have n + (n+1) = m + (m+1), from nat.add_comm (m+1) m ▸ nat.add_comm (n+1) n ▸ this,
  have succ (n + n) = succ (m + m), from this,
  have n + n = m + m, from nat.no_confusion this id,
  have n = m, from bit0_inj this,
  congr_arg (+1) this

protected theorem bit1_inj : ∀ {n m : ℕ}, bit1 n = bit1 m → n = m :=
λ n m h,
have succ (bit0 n) = succ (bit0 m), from nat.bit1_eq_succ_bit0 n ▸ nat.bit1_eq_succ_bit0 m ▸ h,
have bit0 n = bit0 m, from nat.no_confusion this id,
nat.bit0_inj this

protected theorem bit0_ne {n m : ℕ} : n ≠ m → bit0 n ≠ bit0 m :=
λ h₁ h₂, absurd (nat.bit0_inj h₂) h₁

protected theorem bit1_ne {n m : ℕ} : n ≠ m → bit1 n ≠ bit1 m :=
λ h₁ h₂, absurd (nat.bit1_inj h₂) h₁

protected theorem zero_ne_bit0 {n : ℕ} : n ≠ 0 → 0 ≠ bit0 n :=
λ h, ne.symm (nat.bit0_ne_zero h)

protected theorem zero_ne_bit1 (n : ℕ) : 0 ≠ bit1 n :=
ne.symm (nat.bit1_ne_zero n)

protected theorem one_ne_bit0 (n : ℕ) : 1 ≠ bit0 n :=
ne.symm (nat.bit0_ne_one n)

protected theorem one_ne_bit1 {n : ℕ} : n ≠ 0 → 1 ≠ bit1 n :=
λ h, ne.symm (nat.bit1_ne_one h)

protected theorem one_lt_bit1 : ∀ {n : nat}, n ≠ 0 → 1 < bit1 n
| 0        h := absurd rfl h
| (succ n) h :=
  suffices succ 0 < succ (succ (bit1 n)), from
    (nat.bit1_succ_eq n).symm ▸ this,
  succ_lt_succ (zero_lt_succ _)

protected theorem one_lt_bit0 : ∀ {n : nat}, n ≠ 0 → 1 < bit0 n
| 0        h := absurd rfl h
| (succ n) h :=
  suffices succ 0 < succ (succ (bit0 n)), from
    (nat.bit0_succ_eq n).symm ▸ this,
  succ_lt_succ (zero_lt_succ _)

protected lemma bit0_lt {n m : nat} (h : n < m) : bit0 n < bit0 m :=
nat.add_lt_add h h

protected lemma bit1_lt {n m : nat} (h : n < m) : bit1 n < bit1 m :=
succ_lt_succ (nat.add_lt_add h h)

protected lemma bit0_lt_bit1 {n m : nat} (h : n ≤ m) : bit0 n < bit1 m :=
lt_succ_of_le (nat.add_le_add h h)

protected lemma bit1_lt_bit0 : ∀ {n m : nat}, n < m → bit1 n < bit0 m
| n 0        h := absurd h (not_lt_zero _)
| n (succ m) h :=
  have n ≤ m, from le_of_lt_succ h,
  have succ (n + n) ≤ succ (m + m),      from succ_le_succ (add_le_add this this),
  have succ (n + n) ≤ succ m + m,        from (succ_add m m).symm ▸ this,
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

/- power -/

theorem pow_succ (b n : ℕ) : b^(succ n) = b^n * b := rfl

theorem pow_zero (b : ℕ) : b^0 = 1 := rfl

end nat
