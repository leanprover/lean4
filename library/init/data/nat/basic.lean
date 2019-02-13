/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura
-/
prelude
import init.core

notation `ℕ` := nat

namespace nat

@[extern cpp "lean::nat_dec_eq"]
def beq : nat → nat → bool
| zero     zero     := tt
| zero     (succ m) := ff
| (succ n) zero     := ff
| (succ n) (succ m) := beq n m

theorem eq_of_beq_eq_tt : ∀ {n m : nat}, beq n m = tt → n = m
| zero     zero     h := rfl
| zero     (succ m) h := bool.no_confusion h
| (succ n) zero     h := bool.no_confusion h
| (succ n) (succ m) h :=
  have beq n m = tt, from h,
  have n = m, from eq_of_beq_eq_tt this,
  congr_arg succ this

theorem ne_of_beq_eq_ff : ∀ {n m : nat}, beq n m = ff → n ≠ m
| zero     zero     h₁ h₂ := bool.no_confusion h₁
| zero     (succ m) h₁ h₂ := nat.no_confusion h₂
| (succ n) zero     h₁ h₂ := nat.no_confusion h₂
| (succ n) (succ m) h₁ h₂ :=
  have beq n m = ff, from h₁,
  have n ≠ m, from ne_of_beq_eq_ff this,
  nat.no_confusion h₂ (λ h₂, absurd h₂ this)

@[extern cpp "lean::nat_dec_eq"]
protected def dec_eq (n m : @& nat) : decidable (n = m) :=
if h : beq n m = tt then is_true (eq_of_beq_eq_tt h)
else is_false (ne_of_beq_eq_ff (eq_ff_of_ne_tt h))

@[inline] instance : decidable_eq nat :=
{dec_eq := nat.dec_eq}

@[extern cpp "lean::nat_dec_le"]
def ble : nat → nat → bool
| zero     zero     := tt
| zero     (succ m) := tt
| (succ n) zero     := ff
| (succ n) (succ m) := ble n m

protected def le (n m : nat) : Prop :=
ble n m = tt

instance : has_le nat :=
⟨nat.le⟩

protected def lt (n m : nat) : Prop :=
nat.le (succ n) m

instance : has_lt nat :=
⟨nat.lt⟩

@[extern cpp inline "lean::nat_sub(#1, lean::box(1))"]
def pred : nat → nat
| 0     := 0
| (a+1) := a

@[extern cpp "lean::nat_sub"]
protected def sub : (@& nat) → (@& nat) → nat
| a 0     := a
| a (b+1) := pred (sub a b)

@[extern cpp "lean::nat_mul"]
protected def mul : (@& nat) → (@& nat) → nat
| a 0     := 0
| a (b+1) := (mul a b) + a

instance : has_sub nat :=
⟨nat.sub⟩

instance : has_mul nat :=
⟨nat.mul⟩

@[specialize] def {u} repeat_core {α : Type u} (f : nat → α → α) (s : nat) : nat → α → α
| 0         a := a
| (succ n)  a := repeat_core n (f (s - (succ n)) a)

@[inline] def {u} repeat {α : Type u} (f : nat → α → α) (n : nat) (a : α) : α :=
repeat_core f n n a

protected def pow (m : nat) : nat → nat
| 0        := 1
| (succ n) := pow n * m

instance : has_pow nat nat :=
⟨nat.pow⟩

/- nat.add theorems -/

protected theorem zero_add : ∀ n : nat, 0 + n = n
| 0     := rfl
| (n+1) := congr_arg succ (zero_add n)

theorem succ_add : ∀ n m : nat, (succ n) + m = succ (n + m)
| n 0     := rfl
| n (m+1) := congr_arg succ (succ_add n m)

theorem add_succ (n m : nat) : n + succ m = succ (n + m) :=
rfl

protected theorem add_zero (n : nat) : n + 0 = n :=
rfl

theorem add_one (n : nat) : n + 1 = succ n :=
rfl

theorem succ_eq_add_one (n : nat) : succ n = n + 1 :=
rfl

protected theorem add_comm : ∀ n m : nat, n + m = m + n
| n 0     := eq.symm (nat.zero_add n)
| n (m+1) :=
  suffices succ (n + m) = succ (m + n), from
    eq.symm (succ_add m n) ▸ this,
  congr_arg succ (add_comm n m)

protected theorem add_assoc : ∀ n m k : nat, (n + m) + k = n + (m + k)
| n m 0        := rfl
| n m (succ k) := congr_arg succ (add_assoc n m k)

protected theorem add_left_comm : ∀ (n m k : nat), n + (m + k) = m + (n + k) :=
left_comm nat.add nat.add_comm nat.add_assoc

protected theorem add_right_comm : ∀ (n m k : nat), (n + m) + k = (n + k) + m :=
right_comm nat.add nat.add_comm nat.add_assoc

protected theorem add_left_cancel : ∀ {n m k : nat}, n + m = n + k → m = k
| 0        m k h := nat.zero_add m ▸ nat.zero_add k ▸ h
| (succ n) m k h :=
  have n+m = n+k, from
    have succ (n + m) = succ (n + k), from succ_add n m ▸ succ_add n k ▸ h,
    nat.no_confusion this id,
  add_left_cancel this

protected theorem add_right_cancel {n m k : nat} (h : n + m = k + m) : n = k :=
have m + n = m + k, from nat.add_comm n m ▸ nat.add_comm k m ▸ h,
nat.add_left_cancel this

/- nat.mul theorems -/

protected theorem mul_zero (n : nat) : n * 0 = 0 :=
rfl

theorem mul_succ (n m : nat) : n * succ m = n * m + n :=
rfl

protected theorem zero_mul : ∀ (n : nat), 0 * n = 0
| 0        := rfl
| (succ n) := (mul_succ 0 n).symm ▸ (zero_mul n).symm ▸ rfl

theorem succ_mul : ∀ (n m : nat), (succ n) * m = (n * m) + m
| n 0        := rfl
| n (succ m) :=
  have succ (n * m + m + n) = succ (n * m + n + m), from
    congr_arg succ (nat.add_right_comm _ _ _),
  (mul_succ n m).symm ▸ (mul_succ (succ n) m).symm ▸ (succ_mul n m).symm ▸ this

protected theorem mul_comm : ∀ (n m : nat), n * m = m * n
| n 0        := (nat.zero_mul n).symm ▸ (nat.mul_zero n).symm ▸ rfl
| n (succ m) := (mul_succ n m).symm ▸ (succ_mul m n).symm ▸ (mul_comm n m).symm ▸ rfl

protected theorem mul_one : ∀ (n : nat), n * 1 = n :=
nat.zero_add

protected theorem one_mul (n : nat) : 1 * n = n :=
nat.mul_comm n 1 ▸ nat.mul_one n

local infix `◾`:50 := eq.trans

protected theorem left_distrib : ∀ (n m k : nat), n * (m + k) = n * m + n * k
| 0        m k := (nat.zero_mul (m + k)).symm ▸ (nat.zero_mul m).symm ▸ (nat.zero_mul k).symm ▸ rfl
| (succ n) m k :=
  have h₁ : succ n * (m + k) = n * (m + k) + (m + k),              from succ_mul _ _,
  have h₂ : n * (m + k) + (m + k) = (n * m + n * k) + (m + k),     from left_distrib n m k ▸ rfl,
  have h₃ : (n * m + n * k) + (m + k) = n * m + (n * k + (m + k)), from nat.add_assoc _ _ _,
  have h₄ : n * m + (n * k + (m + k)) = n * m + (m + (n * k + k)), from congr_arg (λ x, n*m + x) (nat.add_left_comm _ _ _),
  have h₅ : n * m + (m + (n * k + k)) = (n * m + m) + (n * k + k), from (nat.add_assoc _ _ _).symm,
  have h₆ : (n * m + m) + (n * k + k) = (n * m + m) + succ n * k,  from succ_mul n k ▸ rfl,
  have h₇ : (n * m + m) + succ n * k = succ n * m + succ n * k,    from succ_mul n m ▸ rfl,
  h₁ ◾ h₂ ◾ h₃ ◾ h₄ ◾ h₅ ◾ h₆ ◾ h₇

protected theorem right_distrib (n m k : nat) : (n + m) * k = n * k + m * k :=
have h₁ : (n + m) * k = k * (n + m),     from nat.mul_comm _ _,
have h₂ : k * (n + m) = k * n + k * m,   from nat.left_distrib _ _ _,
have h₃ : k * n + k * m = n * k + k * m, from nat.mul_comm n k ▸ rfl,
have h₄ : n * k + k * m = n * k + m * k, from nat.mul_comm m k ▸ rfl,
h₁ ◾ h₂ ◾ h₃ ◾ h₄

protected theorem mul_assoc : ∀ (n m k : nat), (n * m) * k = n * (m * k)
| n m 0        := rfl
| n m (succ k) :=
  have h₁ : n * m * succ k = n * m * (k + 1),              from rfl,
  have h₂ : n * m * (k + 1) = (n * m * k) + n * m * 1,     from nat.left_distrib _ _ _,
  have h₃ : (n * m * k) + n * m * 1 = (n * m * k) + n * m, from (nat.mul_one (n*m)).symm ▸ rfl,
  have h₄ : (n * m * k) + n * m = (n * (m * k)) + n * m,   from (mul_assoc n m k).symm ▸ rfl,
  have h₅ : (n * (m * k)) + n * m = n * (m * k + m),       from (nat.left_distrib n (m*k) m).symm,
  have h₆ : n * (m * k + m) = n * (m * succ k),            from nat.mul_succ m k ▸ rfl,
h₁ ◾ h₂ ◾ h₃ ◾ h₄ ◾ h₅ ◾ h₆

/- Inequalities -/

protected def le_refl : ∀ n : nat, n ≤ n
| zero     := rfl
| (succ n) := le_refl n

theorem le_succ : ∀ (n : nat), n ≤ succ n
| zero     := rfl
| (succ n) := le_succ n

theorem succ_le_succ {n m : nat} (h : n ≤ m) : succ n ≤ succ m :=
h

theorem succ_lt_succ {n m : nat} : n < m → succ n < succ m :=
succ_le_succ

theorem le_step : ∀ {n m : nat}, n ≤ m → n ≤ succ m
| zero     zero     h := rfl
| zero     (succ n) h := rfl
| (succ n) zero     h := bool.no_confusion h
| (succ n) (succ m) h :=
  have n ≤ m, from h,
  have n ≤ succ m, from le_step this,
  succ_le_succ this

theorem zero_le : ∀ (n : nat), 0 ≤ n
| zero     := rfl
| (succ n) := rfl

theorem zero_lt_succ (n : nat) : 0 < succ n :=
succ_le_succ (zero_le n)

def succ_pos := zero_lt_succ

theorem not_succ_le_zero : ∀ (n : nat), succ n ≤ 0 → false
.

theorem not_lt_zero (n : nat) : ¬ n < 0 :=
not_succ_le_zero n

theorem pred_le_pred : ∀ {n m : nat}, n ≤ m → pred n ≤ pred m
| zero     zero     h := rfl
| zero     (succ n) h := zero_le n
| (succ n) zero     h := bool.no_confusion h
| (succ n) (succ m) h := h

theorem le_of_succ_le_succ {n m : nat} : succ n ≤ succ m → n ≤ m :=
pred_le_pred

@[extern cpp "lean::nat_dec_le"]
instance dec_le (n m : @& nat) : decidable (n ≤ m) :=
dec_eq (ble n m) tt

@[extern cpp "lean::nat_dec_lt"]
instance dec_lt (n m : @& nat) : decidable (n < m) :=
nat.dec_le (succ n) m

protected theorem eq_or_lt_of_le : ∀ {n m: nat}, n ≤ m → n = m ∨ n < m
| zero     zero     h := or.inl rfl
| zero     (succ n) h := or.inr $ zero_le n
| (succ n) zero     h := bool.no_confusion h
| (succ n) (succ m) h :=
  have n ≤ m, from h,
  have n = m ∨ n < m, from eq_or_lt_of_le this,
  or.elim this
   (λ h, or.inl $ congr_arg succ h)
   (λ h, or.inr $ succ_lt_succ h)

theorem lt_succ_of_le {n m : nat} : n ≤ m → n < succ m :=
succ_le_succ

protected theorem sub_zero (n : nat) : n - 0 = n :=
rfl

theorem succ_sub_succ_eq_sub (n m : nat) : succ n - succ m = n - m :=
nat.rec_on m
  (show succ n - succ zero = n - zero, from (eq.refl (succ n - succ zero)))
  (λ m, congr_arg pred)

theorem not_succ_le_self : ∀ n : nat, ¬succ n ≤ n :=
λ n, nat.rec (not_succ_le_zero 0) (λ a b c, b (le_of_succ_le_succ c)) n

protected theorem lt_irrefl (n : nat) : ¬n < n :=
not_succ_le_self n

protected theorem le_trans : ∀ {n m k : nat}, n ≤ m → m ≤ k → n ≤ k
| zero     m        k        h₁ h₂ := zero_le _
| (succ n) zero     k        h₁ h₂ := bool.no_confusion h₁
| (succ n) (succ m) zero     h₁ h₂ := bool.no_confusion h₂
| (succ n) (succ m) (succ k) h₁ h₂ :=
  have h₁' : n ≤ m, from h₁,
  have h₂' : m ≤ k, from h₂,
  have n ≤ k, from le_trans h₁' h₂',
  succ_le_succ this

theorem pred_le : ∀ (n : nat), pred n ≤ n
| zero     := rfl
| (succ n) := le_succ _

theorem pred_lt : ∀ {n : nat}, n ≠ 0 → pred n < n
| zero     h := absurd rfl h
| (succ n) h := lt_succ_of_le (nat.le_refl _)

theorem sub_le (n m : nat) : n - m ≤ n :=
nat.rec_on m (nat.le_refl (n - 0)) (λ m, nat.le_trans (pred_le (n - m)))

theorem sub_lt : ∀ {n m : nat}, 0 < n → 0 < m → n - m < n
| 0     m     h1 h2 := absurd h1 (nat.lt_irrefl 0)
| (n+1) 0     h1 h2 := absurd h2 (nat.lt_irrefl 0)
| (n+1) (m+1) h1 h2 :=
  eq.symm (succ_sub_succ_eq_sub n m) ▸
    show n - m < succ n, from
    lt_succ_of_le (sub_le n m)

protected theorem lt_of_lt_of_le {n m k : nat} : n < m → m ≤ k → n < k :=
nat.le_trans

protected theorem le_of_eq {n m : nat} (p : n = m) : n ≤ m :=
p ▸ nat.le_refl n

theorem le_succ_of_le {n m : nat} (h : n ≤ m) : n ≤ succ m :=
nat.le_trans h (le_succ m)

theorem le_of_succ_le {n m : nat} (h : succ n ≤ m) : n ≤ m :=
nat.le_trans (le_succ n) h

protected theorem le_of_lt {n m : nat} (h : n < m) : n ≤ m :=
le_of_succ_le h

def lt.step {n m : nat} : n < m → n < succ m := le_step

theorem eq_zero_or_pos : ∀ (n : nat), n = 0 ∨ n > 0
| 0     := or.inl rfl
| (n+1) := or.inr (succ_pos _)

protected theorem lt_trans {n m k : nat} (h₁ : n < m) : m < k → n < k :=
nat.le_trans (le_step h₁)

protected theorem lt_of_le_of_lt {n m k : nat} (h₁ : n ≤ m) : m < k → n < k :=
nat.le_trans (succ_le_succ h₁)

def lt.base (n : nat) : n < succ n := nat.le_refl (succ n)

theorem lt_succ_self (n : nat) : n < succ n := lt.base n

protected theorem le_antisymm : ∀ {n m : nat}, n ≤ m → m ≤ n → n = m
| zero     zero     h₁ h₂ := rfl
| (succ n) zero     h₁ h₂ := bool.no_confusion h₁
| zero     (succ m) h₁ h₂ := bool.no_confusion h₂
| (succ n) (succ m) h₁ h₂ :=
  have h₁' : n ≤ m, from h₁,
  have h₂' : m ≤ n, from h₂,
  have n = m, from le_antisymm h₁' h₂',
  congr_arg succ this

protected theorem lt_or_ge : ∀ (n m : nat), n < m ∨ n ≥ m
| n 0     := or.inr (zero_le n)
| n (m+1) :=
  match lt_or_ge n m with
  | or.inl h := or.inl (le_succ_of_le h)
  | or.inr h :=
    match nat.eq_or_lt_of_le h with
    | or.inl h1 := or.inl (h1 ▸ lt_succ_self m)
    | or.inr h1 := or.inr h1

protected theorem le_total (m n : nat) : m ≤ n ∨ n ≤ m :=
or.elim (nat.lt_or_ge m n)
  (λ h, or.inl (nat.le_of_lt h))
  or.inr

protected theorem lt_of_le_and_ne {m n : nat} (h1 : m ≤ n) : m ≠ n → m < n :=
resolve_right (or.swap (nat.eq_or_lt_of_le h1))

theorem eq_zero_of_le_zero {n : nat} (h : n ≤ 0) : n = 0 :=
nat.le_antisymm h (zero_le _)

theorem lt_of_succ_lt {n m : nat} : succ n < m → n < m :=
le_of_succ_le

theorem lt_of_succ_lt_succ {n m : nat} : succ n < succ m → n < m :=
le_of_succ_le_succ

theorem lt_of_succ_le {n m : nat} (h : succ n ≤ m) : n < m :=
h

theorem succ_le_of_lt {n m : nat} (h : n < m) : succ n ≤ m :=
h

theorem lt_or_eq_or_le_succ {m n : nat} (h : m ≤ succ n) : m ≤ n ∨ m = succ n :=
decidable.by_cases
  (λ h' : m = succ n, or.inr h')
  (λ h' : m ≠ succ n,
     have m < succ n, from nat.lt_of_le_and_ne h h',
     have succ m ≤ succ n, from succ_le_of_lt this,
     or.inl (le_of_succ_le_succ this))

theorem le_add_right : ∀ (n k : nat), n ≤ n + k
| n 0     := nat.le_refl n
| n (k+1) := le_succ_of_le (le_add_right n k)

theorem le_add_left (n m : nat): n ≤ m + n :=
nat.add_comm n m ▸ le_add_right n m

theorem le.dest : ∀ {n m : nat}, n ≤ m → ∃ k, n + k = m
| zero     zero     h := ⟨0, rfl⟩
| zero     (succ n) h := ⟨succ n, show 0 + succ n = succ n, from (nat.add_comm 0 (succ n)).symm ▸ rfl⟩
| (succ n) zero     h := bool.no_confusion h
| (succ n) (succ m) h :=
  have n ≤ m, from h,
  have ∃ k, n + k = m, from le.dest this,
  match this with
  | ⟨k, h⟩ := ⟨k, show succ n + k = succ m, from ((succ_add n k).symm ▸ h ▸ rfl)⟩

theorem le.intro {n m k : nat} (h : n + k = m) : n ≤ m :=
h ▸ le_add_right n k

protected theorem not_le_of_gt {n m : nat} (h : n > m) : ¬ n ≤ m :=
λ h₁, or.elim (nat.lt_or_ge n m)
  (λ h₂, absurd (nat.lt_trans h h₂) (nat.lt_irrefl _))
  (λ h₂, have heq : n = m, from nat.le_antisymm h₁ h₂, absurd (@eq.subst _ _ _ _ heq h) (nat.lt_irrefl m))

theorem gt_of_not_le {n m : nat} (h : ¬ n ≤ m) : n > m :=
or.elim (nat.lt_or_ge m n)
  (λ h₁, h₁)
  (λ h₁, absurd h₁ h)

protected theorem lt_of_le_of_ne {n m : nat} (h₁ : n ≤ m) (h₂ : n ≠ m) : n < m :=
or.elim (nat.lt_or_ge n m)
  (λ h₃, h₃)
  (λ h₃, absurd (nat.le_antisymm h₁ h₃) h₂)

protected theorem add_le_add_left {n m : nat} (h : n ≤ m) (k : nat) : k + n ≤ k + m :=
match le.dest h with
| ⟨w, hw⟩ :=
  have h₁ : k + n + w = k + (n + w), from nat.add_assoc _ _ _,
  have h₂ : k + (n + w) = k + m,     from congr_arg _ hw,
  le.intro $ h₁ ◾ h₂

protected theorem add_le_add_right {n m : nat} (h : n ≤ m) (k : nat) : n + k ≤ m + k :=
have h₁ : n + k = k + n, from nat.add_comm _ _,
have h₂ : k + n ≤ k + m, from nat.add_le_add_left h k,
have h₃ : k + m = m + k, from nat.add_comm _ _,
trans_rel_left (≤) (trans_rel_right (≤) h₁ h₂) h₃

protected theorem add_lt_add_left {n m : nat} (h : n < m) (k : nat) : k + n < k + m :=
lt_of_succ_le (add_succ k n ▸ nat.add_le_add_left (succ_le_of_lt h) k)

protected theorem add_lt_add_right {n m : nat} (h : n < m) (k : nat) : n + k < m + k :=
nat.add_comm k m ▸ nat.add_comm k n ▸ nat.add_lt_add_left h k

protected theorem zero_lt_one : 0 < (1:nat) :=
zero_lt_succ 0

theorem le_of_lt_succ {m n : nat} : m < succ n → m ≤ n :=
le_of_succ_le_succ

theorem add_le_add {a b c d : nat} (h₁ : a ≤ b) (h₂ : c ≤ d) : a + c ≤ b + d :=
nat.le_trans (nat.add_le_add_right h₁ c) (nat.add_le_add_left h₂ b)

theorem add_lt_add {a b c d : nat} (h₁ : a < b) (h₂ : c < d) : a + c < b + d :=
nat.lt_trans (nat.add_lt_add_right h₁ c) (nat.add_lt_add_left h₂ b)

/- Basic theorems for comparing numerals -/

theorem nat_zero_eq_zero : nat.zero = 0 :=
rfl

protected theorem one_ne_zero : 1 ≠ (0 : nat) :=
assume h, nat.no_confusion h

protected theorem zero_ne_one : 0 ≠ (1 : nat) :=
assume h, nat.no_confusion h

theorem succ_ne_zero (n : nat) : succ n ≠ 0 :=
assume h, nat.no_confusion h

protected theorem bit0_succ_eq (n : nat) : bit0 (succ n) = succ (succ (bit0 n)) :=
show succ (succ n + n) = succ (succ (n + n)), from
congr_arg succ (succ_add n n)

protected theorem zero_lt_bit0 : ∀ {n : nat}, n ≠ 0 → 0 < bit0 n
| 0        h := absurd rfl h
| (succ n) h :=
  have h₁ : 0 < succ (succ (bit0 n)),             from zero_lt_succ _,
  have h₂ : succ (succ (bit0 n)) = bit0 (succ n), from (nat.bit0_succ_eq n).symm,
  trans_rel_left (<) h₁ h₂

protected theorem zero_lt_bit1 (n : nat) : 0 < bit1 n :=
zero_lt_succ _

protected theorem bit0_ne_zero : ∀ {n : nat}, n ≠ 0 → bit0 n ≠ 0
| 0     h := absurd rfl h
| (n+1) h :=
  suffices (n+1) + (n+1) ≠ 0, from this,
  suffices succ ((n+1) + n) ≠ 0, from this,
  λ h, nat.no_confusion h

protected theorem bit1_ne_zero (n : nat) : bit1 n ≠ 0 :=
show succ (n + n) ≠ 0, from
λ h, nat.no_confusion h

protected theorem bit1_eq_succ_bit0 (n : nat) : bit1 n = succ (bit0 n) :=
rfl

protected theorem bit1_succ_eq (n : nat) : bit1 (succ n) = succ (succ (bit1 n)) :=
eq.trans (nat.bit1_eq_succ_bit0 (succ n)) (congr_arg succ (nat.bit0_succ_eq n))

protected theorem bit1_ne_one : ∀ {n : nat}, n ≠ 0 → bit1 n ≠ 1
| 0     h h1 := absurd rfl h
| (n+1) h h1 := nat.no_confusion h1 (λ h2, absurd h2 (succ_ne_zero _))

protected theorem bit0_ne_one : ∀ n : nat, bit0 n ≠ 1
| 0     h := absurd h (ne.symm nat.one_ne_zero)
| (n+1) h :=
  have h1 : succ (succ (n + n)) = 1, from succ_add n n ▸ h,
  nat.no_confusion h1
    (λ h2, absurd h2 (succ_ne_zero (n + n)))

protected theorem add_self_ne_one : ∀ (n : nat), n + n ≠ 1
| 0     h := nat.no_confusion h
| (n+1) h :=
  have h1 : succ (succ (n + n)) = 1, from succ_add n n ▸ h,
  nat.no_confusion h1 (λ h2, absurd h2 (nat.succ_ne_zero (n + n)))

protected theorem bit1_ne_bit0 : ∀ (n m : nat), bit1 n ≠ bit0 m
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

protected theorem bit0_ne_bit1 : ∀ (n m : nat), bit0 n ≠ bit1 m :=
λ n m : nat, ne.symm (nat.bit1_ne_bit0 m n)

protected theorem bit0_inj : ∀ {n m : nat}, bit0 n = bit0 m → n = m
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

protected theorem bit1_inj : ∀ {n m : nat}, bit1 n = bit1 m → n = m :=
λ n m h,
have succ (bit0 n) = succ (bit0 m), from nat.bit1_eq_succ_bit0 n ▸ nat.bit1_eq_succ_bit0 m ▸ h,
have bit0 n = bit0 m, from nat.no_confusion this id,
nat.bit0_inj this

protected theorem bit0_ne {n m : nat} : n ≠ m → bit0 n ≠ bit0 m :=
λ h₁ h₂, absurd (nat.bit0_inj h₂) h₁

protected theorem bit1_ne {n m : nat} : n ≠ m → bit1 n ≠ bit1 m :=
λ h₁ h₂, absurd (nat.bit1_inj h₂) h₁

protected theorem zero_ne_bit0 {n : nat} : n ≠ 0 → 0 ≠ bit0 n :=
λ h, ne.symm (nat.bit0_ne_zero h)

protected theorem zero_ne_bit1 (n : nat) : 0 ≠ bit1 n :=
ne.symm (nat.bit1_ne_zero n)

protected theorem one_ne_bit0 (n : nat) : 1 ≠ bit0 n :=
ne.symm (nat.bit0_ne_one n)

protected theorem one_ne_bit1 {n : nat} : n ≠ 0 → 1 ≠ bit1 n :=
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

protected theorem bit0_lt {n m : nat} (h : n < m) : bit0 n < bit0 m :=
nat.add_lt_add h h

protected theorem bit1_lt {n m : nat} (h : n < m) : bit1 n < bit1 m :=
succ_lt_succ (nat.add_lt_add h h)

protected theorem bit0_lt_bit1 {n m : nat} (h : n ≤ m) : bit0 n < bit1 m :=
lt_succ_of_le (nat.add_le_add h h)

protected theorem bit1_lt_bit0 : ∀ {n m : nat}, n < m → bit1 n < bit0 m
| n 0        h := absurd h (not_lt_zero _)
| n (succ m) h :=
  have n ≤ m, from le_of_lt_succ h,
  have succ (n + n) ≤ succ (m + m),      from succ_le_succ (add_le_add this this),
  have succ (n + n) ≤ succ m + m,        from (succ_add m m).symm ▸ this,
  show succ (n + n) < succ (succ m + m), from lt_succ_of_le this

protected theorem one_le_bit1 (n : nat) : 1 ≤ bit1 n :=
show 1 ≤ succ (bit0 n), from
succ_le_succ (zero_le (bit0 n))

protected theorem one_le_bit0 : ∀ (n : nat), n ≠ 0 → 1 ≤ bit0 n
| 0     h := absurd rfl h
| (n+1) h :=
  suffices 1 ≤ succ (succ (bit0 n)), from
    eq.symm (nat.bit0_succ_eq n) ▸ this,
  succ_le_succ (zero_le (succ (bit0 n)))

/- mul + order -/

theorem mul_le_mul_left {n m : nat} (k : nat) (h : n ≤ m) : k * n ≤ k * m :=
match le.dest h with
| ⟨l, hl⟩ :=
  have k * n + k * l = k * m, from nat.left_distrib k n l ▸ hl.symm ▸ rfl,
  le.intro this

theorem mul_le_mul_right {n m : nat} (k : nat) (h : n ≤ m) : n * k ≤ m * k :=
nat.mul_comm k m ▸ nat.mul_comm k n ▸ mul_le_mul_left k h

protected theorem mul_le_mul {n₁ m₁ n₂ m₂ : nat} (h₁ : n₁ ≤ n₂) (h₂ : m₁ ≤ m₂) : n₁ * m₁ ≤ n₂ * m₂ :=
nat.le_trans (mul_le_mul_right _ h₁) (mul_le_mul_left _ h₂)

protected theorem mul_lt_mul_of_pos_left {n m k : nat} (h : n < m) (hk : k > 0) : k * n < k * m :=
nat.lt_of_lt_of_le (nat.add_lt_add_left hk _) (nat.mul_succ k n ▸ nat.mul_le_mul_left k (succ_le_of_lt h))

protected theorem mul_lt_mul_of_pos_right {n m k : nat} (h : n < m) (hk : k > 0) : n * k < m * k :=
nat.mul_comm k m ▸ nat.mul_comm k n ▸ nat.mul_lt_mul_of_pos_left h hk

protected theorem mul_pos {n m : nat} (ha : n > 0) (hb : m > 0) : n * m > 0 :=
have h : 0 * m < n * m, from nat.mul_lt_mul_of_pos_right ha hb,
nat.zero_mul m ▸ h

/- power -/

theorem pow_succ (n m : nat) : n^(succ m) = n^m * n :=
rfl

theorem pow_zero (n : nat) : n^0 = 1 := rfl

theorem pow_le_pow_of_le_left {n m : nat} (h : n ≤ m) : ∀ i : nat, n^i ≤ m^i
| 0        := nat.le_refl _
| (succ i) := nat.mul_le_mul (pow_le_pow_of_le_left i) h

theorem pow_le_pow_of_le_right {n : nat} (hx : n > 0) {i : nat} : ∀ {j}, i ≤ j → n^i ≤ n^j
| 0        h :=
  have i = 0, from eq_zero_of_le_zero h,
  this.symm ▸ nat.le_refl _
| (succ j) h :=
  or.elim (lt_or_eq_or_le_succ h)
    (λ h, show n^i ≤ n^j * n, from
          suffices n^i * 1 ≤ n^j * n, from nat.mul_one (n^i) ▸ this,
          nat.mul_le_mul (pow_le_pow_of_le_right h) hx)
    (λ h, h.symm ▸ nat.le_refl _)

theorem pos_pow_of_pos {n : nat} (m : nat) (h : 0 < n) : 0 < n^m :=
pow_le_pow_of_le_right h (nat.zero_le _)

/- Max -/

protected def max (n m : nat) : nat :=
if n ≤ m then m else n

end nat
