/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura
-/
prelude
import Init.SimpLemmas
set_option linter.missingDocs true -- keep it documented
universe u

namespace Nat

/--
`Nat.fold` evaluates `f` on the numbers up to `n` exclusive, in increasing order:
* `Nat.fold f 3 init = init |> f 0 |> f 1 |> f 2`
-/
@[specialize] def fold {α : Type u} (f : Nat → α → α) : (n : Nat) → (init : α) → α
  | 0,      a => a
  | succ n, a => f n (fold f n a)

/-- Tail-recursive version of `Nat.fold`. -/
@[inline] def foldTR {α : Type u} (f : Nat → α → α) (n : Nat) (init : α) : α :=
  let rec @[specialize] loop
    | 0,      a => a
    | succ m, a => loop m (f (n - succ m) a)
  loop n init

/--
`Nat.foldRev` evaluates `f` on the numbers up to `n` exclusive, in decreasing order:
* `Nat.foldRev f 3 init = f 0 <| f 1 <| f 2 <| init`
-/
@[specialize] def foldRev {α : Type u} (f : Nat → α → α) : (n : Nat) → (init : α) → α
  | 0,      a => a
  | succ n, a => foldRev f n (f n a)

/-- `any f n = true` iff there is `i in [0, n-1]` s.t. `f i = true` -/
@[specialize] def any (f : Nat → Bool) : Nat → Bool
  | 0      => false
  | succ n => any f n || f n

/-- Tail-recursive version of `Nat.any`. -/
@[inline] def anyTR (f : Nat → Bool) (n : Nat) : Bool :=
  let rec @[specialize] loop : Nat → Bool
    | 0      => false
    | succ m => f (n - succ m) || loop m
  loop n

/-- `all f n = true` iff every `i in [0, n-1]` satisfies `f i = true` -/
@[specialize] def all (f : Nat → Bool) : Nat → Bool
  | 0      => true
  | succ n => all f n && f n

/-- Tail-recursive version of `Nat.all`. -/
@[inline] def allTR (f : Nat → Bool) (n : Nat) : Bool :=
  let rec @[specialize] loop : Nat → Bool
    | 0      => true
    | succ m => f (n - succ m) && loop m
  loop n

/--
`Nat.repeat f n a` is `f^(n) a`; that is, it iterates `f` `n` times on `a`.
* `Nat.repeat f 3 a = f <| f <| f <| a`
-/
@[specialize] def repeat {α : Type u} (f : α → α) : (n : Nat) → (a : α) → α
  | 0,      a => a
  | succ n, a => f (repeat f n a)

/-- Tail-recursive version of `Nat.repeat`. -/
@[inline] def repeatTR {α : Type u} (f : α → α) (n : Nat) (a : α) : α :=
  let rec @[specialize] loop
    | 0,      a => a
    | succ n, a => loop n (f a)
  loop n a

/-- Boolean less-than of natural numbers. -/
def blt (a b : Nat) : Bool :=
  ble a.succ b

attribute [simp] Nat.zero_le

/-! # Helper "packing" theorems -/

@[simp] theorem zero_eq : Nat.zero = 0 := rfl
@[simp] theorem add_eq : Nat.add x y = x + y := rfl
@[simp] theorem mul_eq : Nat.mul x y = x * y := rfl
@[simp] theorem sub_eq : Nat.sub x y = x - y := rfl
@[simp] theorem lt_eq : Nat.lt x y = (x < y) := rfl
@[simp] theorem le_eq : Nat.le x y = (x ≤ y) := rfl

/-! # Helper Bool relation theorems -/

@[simp] theorem beq_refl (a : Nat) : Nat.beq a a = true := by
  induction a with simp [Nat.beq]
  | succ a ih => simp [ih]

@[simp] theorem beq_eq : (Nat.beq x y = true) = (x = y) := propext <| Iff.intro Nat.eq_of_beq_eq_true (fun h => h ▸ (Nat.beq_refl x))
@[simp] theorem ble_eq : (Nat.ble x y = true) = (x ≤ y) := propext <| Iff.intro Nat.le_of_ble_eq_true Nat.ble_eq_true_of_le
@[simp] theorem blt_eq : (Nat.blt x y = true) = (x < y) := propext <| Iff.intro Nat.le_of_ble_eq_true Nat.ble_eq_true_of_le

instance : LawfulBEq Nat where
  eq_of_beq h := Nat.eq_of_beq_eq_true h
  rfl := by simp [BEq.beq]

@[simp] theorem beq_eq_true_eq (a b : Nat) : ((a == b) = true) = (a = b) := propext <| Iff.intro eq_of_beq (fun h => by subst h; apply LawfulBEq.rfl)
@[simp] theorem not_beq_eq_true_eq (a b : Nat) : ((!(a == b)) = true) = ¬(a = b) :=
  propext <| Iff.intro
    (fun h₁ h₂ => by subst h₂; rw [LawfulBEq.rfl] at h₁; contradiction)
    (fun h =>
      have : ¬ ((a == b) = true) := fun h' => absurd (eq_of_beq h') h
      by simp [this])

/-! # Nat.add theorems -/

@[simp] protected theorem zero_add : ∀ (n : Nat), 0 + n = n
  | 0   => rfl
  | n+1 => congrArg succ (Nat.zero_add n)

theorem succ_add : ∀ (n m : Nat), (succ n) + m = succ (n + m)
  | _, 0   => rfl
  | n, m+1 => congrArg succ (succ_add n m)

theorem add_succ (n m : Nat) : n + succ m = succ (n + m) :=
  rfl

theorem add_one (n : Nat) : n + 1 = succ n :=
  rfl

theorem succ_eq_add_one (n : Nat) : succ n = n + 1 :=
  rfl

protected theorem add_comm : ∀ (n m : Nat), n + m = m + n
  | n, 0   => Eq.symm (Nat.zero_add n)
  | n, m+1 => by
    have : succ (n + m) = succ (m + n) := by apply congrArg; apply Nat.add_comm
    rw [succ_add m n]
    apply this

protected theorem add_assoc : ∀ (n m k : Nat), (n + m) + k = n + (m + k)
  | _, _, 0      => rfl
  | n, m, succ k => congrArg succ (Nat.add_assoc n m k)

protected theorem add_left_comm (n m k : Nat) : n + (m + k) = m + (n + k) := by
  rw [← Nat.add_assoc, Nat.add_comm n m, Nat.add_assoc]

protected theorem add_right_comm (n m k : Nat) : (n + m) + k = (n + k) + m := by
  rw [Nat.add_assoc, Nat.add_comm m k, ← Nat.add_assoc]

protected theorem add_left_cancel {n m k : Nat} : n + m = n + k → m = k := by
  induction n with
  | zero => simp; intros; assumption
  | succ n ih => simp [succ_add]; intro h; apply ih h

protected theorem add_right_cancel {n m k : Nat} (h : n + m = k + m) : n = k := by
  rw [Nat.add_comm n m, Nat.add_comm k m] at h
  apply Nat.add_left_cancel h

/-! # Nat.mul theorems -/

@[simp] protected theorem mul_zero (n : Nat) : n * 0 = 0 :=
  rfl

theorem mul_succ (n m : Nat) : n * succ m = n * m + n :=
  rfl

@[simp] protected theorem zero_mul : ∀ (n : Nat), 0 * n = 0
  | 0      => rfl
  | succ n => mul_succ 0 n ▸ (Nat.zero_mul n).symm ▸ rfl

theorem succ_mul (n m : Nat) : (succ n) * m = (n * m) + m := by
  induction m with
  | zero => rfl
  | succ m ih => rw [mul_succ, add_succ, ih, mul_succ, add_succ, Nat.add_right_comm]

protected theorem mul_comm : ∀ (n m : Nat), n * m = m * n
  | n, 0      => (Nat.zero_mul n).symm ▸ (Nat.mul_zero n).symm ▸ rfl
  | n, succ m => (mul_succ n m).symm ▸ (succ_mul m n).symm ▸ (Nat.mul_comm n m).symm ▸ rfl

@[simp] protected theorem mul_one : ∀ (n : Nat), n * 1 = n :=
  Nat.zero_add

@[simp] protected theorem one_mul (n : Nat) : 1 * n = n :=
  Nat.mul_comm n 1 ▸ Nat.mul_one n

protected theorem left_distrib (n m k : Nat) : n * (m + k) = n * m + n * k := by
  induction n generalizing m k with
  | zero      => repeat rw [Nat.zero_mul]
  | succ n ih => simp [succ_mul, ih]; rw [Nat.add_assoc, Nat.add_assoc (n*m)]; apply congrArg; apply Nat.add_left_comm

protected theorem right_distrib (n m k : Nat) : (n + m) * k = n * k + m * k := by
  rw [Nat.mul_comm, Nat.left_distrib]; simp [Nat.mul_comm]

protected theorem mul_add (n m k : Nat) : n * (m + k) = n * m + n * k :=
  Nat.left_distrib n m k

protected theorem add_mul (n m k : Nat) : (n + m) * k = n * k + m * k :=
  Nat.right_distrib n m k

protected theorem mul_assoc : ∀ (n m k : Nat), (n * m) * k = n * (m * k)
  | n, m, 0      => rfl
  | n, m, succ k => by simp [mul_succ, Nat.mul_assoc n m k, Nat.left_distrib]

protected theorem mul_left_comm (n m k : Nat) : n * (m * k) = m * (n * k) := by
  rw [← Nat.mul_assoc, Nat.mul_comm n m, Nat.mul_assoc]

/-! # Inequalities -/

attribute [simp] Nat.le_refl

theorem succ_lt_succ {n m : Nat} : n < m → succ n < succ m :=
  succ_le_succ

theorem lt_succ_of_le {n m : Nat} : n ≤ m → n < succ m :=
  succ_le_succ

@[simp] protected theorem sub_zero (n : Nat) : n - 0 = n :=
  rfl

theorem succ_sub_succ_eq_sub (n m : Nat) : succ n - succ m = n - m := by
  induction m with
  | zero      => exact rfl
  | succ m ih => apply congrArg pred ih

theorem pred_le : ∀ (n : Nat), pred n ≤ n
  | zero   => Nat.le.refl
  | succ _ => le_succ _

theorem pred_lt : ∀ {n : Nat}, n ≠ 0 → pred n < n
  | zero,   h => absurd rfl h
  | succ _, _ => lt_succ_of_le (Nat.le_refl _)

theorem sub_le (n m : Nat) : n - m ≤ n := by
  induction m with
  | zero      => exact Nat.le_refl (n - 0)
  | succ m ih => apply Nat.le_trans (pred_le (n - m)) ih

theorem sub_lt : ∀ {n m : Nat}, 0 < n → 0 < m → n - m < n
  | 0,   _,   h1, _  => absurd h1 (Nat.lt_irrefl 0)
  | _+1, 0,   _, h2  => absurd h2 (Nat.lt_irrefl 0)
  | n+1, m+1, _,  _  =>
    Eq.symm (succ_sub_succ_eq_sub n m) ▸
      show n - m < succ n from
      lt_succ_of_le (sub_le n m)

theorem sub_succ (n m : Nat) : n - succ m = pred (n - m) :=
  rfl

theorem succ_sub_succ (n m : Nat) : succ n - succ m = n - m :=
  succ_sub_succ_eq_sub n m

@[simp] protected theorem sub_self : ∀ (n : Nat), n - n = 0
  | 0        => by rw [Nat.sub_zero]
  | (succ n) => by rw [succ_sub_succ, Nat.sub_self n]

theorem sub_add_eq (a b c : Nat) : a - (b + c) = a - b - c := by
  induction c with
  | zero => simp
  | succ c ih => simp [Nat.add_succ, Nat.sub_succ, ih]

protected theorem lt_of_lt_of_le {n m k : Nat} : n < m → m ≤ k → n < k :=
  Nat.le_trans

protected theorem lt_of_lt_of_eq {n m k : Nat} : n < m → m = k → n < k :=
  fun h₁ h₂ => h₂ ▸ h₁

instance : Trans (. < . : Nat → Nat → Prop) (. < . : Nat → Nat → Prop) (. < . : Nat → Nat → Prop) where
  trans := Nat.lt_trans

instance : Trans (. ≤ . : Nat → Nat → Prop) (. ≤ . : Nat → Nat → Prop) (. ≤ . : Nat → Nat → Prop) where
  trans := Nat.le_trans

instance : Trans (. < . : Nat → Nat → Prop) (. ≤ . : Nat → Nat → Prop) (. < . : Nat → Nat → Prop) where
  trans := Nat.lt_of_lt_of_le

instance : Trans (. ≤ . : Nat → Nat → Prop) (. < . : Nat → Nat → Prop) (. < . : Nat → Nat → Prop) where
  trans := Nat.lt_of_le_of_lt

protected theorem le_of_eq {n m : Nat} (p : n = m) : n ≤ m :=
  p ▸ Nat.le_refl n

theorem le_of_succ_le {n m : Nat} (h : succ n ≤ m) : n ≤ m :=
  Nat.le_trans (le_succ n) h

protected theorem le_of_lt {n m : Nat} (h : n < m) : n ≤ m :=
  le_of_succ_le h

theorem lt.step {n m : Nat} : n < m → n < succ m := le_step

theorem eq_zero_or_pos : ∀ (n : Nat), n = 0 ∨ n > 0
  | 0   => Or.inl rfl
  | _+1 => Or.inr (succ_pos _)

theorem lt.base (n : Nat) : n < succ n := Nat.le_refl (succ n)

theorem lt_succ_self (n : Nat) : n < succ n := lt.base n

protected theorem le_total (m n : Nat) : m ≤ n ∨ n ≤ m :=
  match Nat.lt_or_ge m n with
  | Or.inl h => Or.inl (Nat.le_of_lt h)
  | Or.inr h => Or.inr h

theorem eq_zero_of_le_zero {n : Nat} (h : n ≤ 0) : n = 0 :=
  Nat.le_antisymm h (zero_le _)

theorem lt_of_succ_lt {n m : Nat} : succ n < m → n < m :=
  le_of_succ_le

theorem lt_of_succ_lt_succ {n m : Nat} : succ n < succ m → n < m :=
  le_of_succ_le_succ

theorem lt_of_succ_le {n m : Nat} (h : succ n ≤ m) : n < m :=
  h

theorem succ_le_of_lt {n m : Nat} (h : n < m) : succ n ≤ m :=
  h

theorem zero_lt_of_lt : {a b : Nat} → a < b → 0 < b
  | 0,   _, h => h
  | a+1, b, h =>
    have : a < b := Nat.lt_trans (Nat.lt_succ_self _) h
    zero_lt_of_lt this

theorem zero_lt_of_ne_zero {a : Nat} (h : a ≠ 0) : 0 < a := by
  match a with
  | 0 => contradiction
  | a+1 => apply Nat.zero_lt_succ

attribute [simp] Nat.lt_irrefl

theorem ne_of_lt {a b : Nat} (h : a < b) : a ≠ b :=
  fun he => absurd (he ▸ h) (Nat.lt_irrefl a)

theorem le_or_eq_of_le_succ {m n : Nat} (h : m ≤ succ n) : m ≤ n ∨ m = succ n :=
  Decidable.byCases
    (fun (h' : m = succ n) => Or.inr h')
    (fun (h' : m ≠ succ n) =>
       have : m < succ n := Nat.lt_of_le_of_ne h h'
       have : succ m ≤ succ n := succ_le_of_lt this
       Or.inl (le_of_succ_le_succ this))

theorem le_add_right : ∀ (n k : Nat), n ≤ n + k
  | n, 0   => Nat.le_refl n
  | n, k+1 => le_succ_of_le (le_add_right n k)

theorem le_add_left (n m : Nat): n ≤ m + n :=
  Nat.add_comm n m ▸ le_add_right n m

theorem le.dest : ∀ {n m : Nat}, n ≤ m → Exists (fun k => n + k = m)
  | zero,   zero,   _ => ⟨0, rfl⟩
  | zero,   succ n, _ => ⟨succ n, Nat.add_comm 0 (succ n) ▸ rfl⟩
  | succ _, zero,   h => absurd h (not_succ_le_zero _)
  | succ n, succ m, h =>
    have : n ≤ m := Nat.le_of_succ_le_succ h
    have : Exists (fun k => n + k = m) := dest this
    match this with
    | ⟨k, h⟩ => ⟨k, show succ n + k = succ m from ((succ_add n k).symm ▸ h ▸ rfl)⟩

theorem le.intro {n m k : Nat} (h : n + k = m) : n ≤ m :=
  h ▸ le_add_right n k

protected theorem not_le_of_gt {n m : Nat} (h : n > m) : ¬ n ≤ m := fun h₁ =>
  match Nat.lt_or_ge n m with
  | Or.inl h₂ => absurd (Nat.lt_trans h h₂) (Nat.lt_irrefl _)
  | Or.inr h₂ =>
    have Heq : n = m := Nat.le_antisymm h₁ h₂
    absurd (@Eq.subst _ _ _ _ Heq h) (Nat.lt_irrefl m)

theorem gt_of_not_le {n m : Nat} (h : ¬ n ≤ m) : n > m :=
  match Nat.lt_or_ge m n with
  | Or.inl h₁ => h₁
  | Or.inr h₁ => absurd h₁ h

theorem ge_of_not_lt {n m : Nat} (h : ¬ n < m) : n ≥ m :=
  match Nat.lt_or_ge n m with
  | Or.inl h₁ => absurd h₁ h
  | Or.inr h₁ => h₁

instance : Antisymm ( . ≤ . : Nat → Nat → Prop) where
  antisymm h₁ h₂ := Nat.le_antisymm h₁ h₂

instance : Antisymm (¬ . < . : Nat → Nat → Prop) where
  antisymm h₁ h₂ := Nat.le_antisymm (Nat.ge_of_not_lt h₂) (Nat.ge_of_not_lt h₁)

protected theorem add_le_add_left {n m : Nat} (h : n ≤ m) (k : Nat) : k + n ≤ k + m :=
  match le.dest h with
  | ⟨w, hw⟩ =>
    have h₁ : k + n + w = k + (n + w) := Nat.add_assoc ..
    have h₂ : k + (n + w) = k + m     := congrArg _ hw
    le.intro <| h₁.trans h₂

protected theorem add_le_add_right {n m : Nat} (h : n ≤ m) (k : Nat) : n + k ≤ m + k := by
  rw [Nat.add_comm n k, Nat.add_comm m k]
  apply Nat.add_le_add_left
  assumption

protected theorem add_lt_add_left {n m : Nat} (h : n < m) (k : Nat) : k + n < k + m :=
  lt_of_succ_le (add_succ k n ▸ Nat.add_le_add_left (succ_le_of_lt h) k)

protected theorem add_lt_add_right {n m : Nat} (h : n < m) (k : Nat) : n + k < m + k :=
  Nat.add_comm k m ▸ Nat.add_comm k n ▸ Nat.add_lt_add_left h k

protected theorem zero_lt_one : 0 < (1:Nat) :=
  zero_lt_succ 0

theorem add_le_add {a b c d : Nat} (h₁ : a ≤ b) (h₂ : c ≤ d) : a + c ≤ b + d :=
  Nat.le_trans (Nat.add_le_add_right h₁ c) (Nat.add_le_add_left h₂ b)

theorem add_lt_add {a b c d : Nat} (h₁ : a < b) (h₂ : c < d) : a + c < b + d :=
  Nat.lt_trans (Nat.add_lt_add_right h₁ c) (Nat.add_lt_add_left h₂ b)

protected theorem le_of_add_le_add_left {a b c : Nat} (h : a + b ≤ a + c) : b ≤ c := by
  match le.dest h with
  | ⟨d, hd⟩ =>
    apply @le.intro _ _ d
    rw [Nat.add_assoc] at hd
    apply Nat.add_left_cancel hd

protected theorem le_of_add_le_add_right {a b c : Nat} : a + b ≤ c + b → a ≤ c := by
  rw [Nat.add_comm _ b, Nat.add_comm _ b]
  apply Nat.le_of_add_le_add_left

/-! # Basic theorems for comparing numerals -/

theorem ctor_eq_zero : Nat.zero = 0 :=
  rfl

protected theorem one_ne_zero : 1 ≠ (0 : Nat) :=
  fun h => Nat.noConfusion h

protected theorem zero_ne_one : 0 ≠ (1 : Nat) :=
  fun h => Nat.noConfusion h

theorem succ_ne_zero (n : Nat) : succ n ≠ 0 :=
  fun h => Nat.noConfusion h

/-! # mul + order -/

theorem mul_le_mul_left {n m : Nat} (k : Nat) (h : n ≤ m) : k * n ≤ k * m :=
  match le.dest h with
  | ⟨l, hl⟩ =>
    have : k * n + k * l = k * m := Nat.left_distrib k n l ▸ hl.symm ▸ rfl
    le.intro this

theorem mul_le_mul_right {n m : Nat} (k : Nat) (h : n ≤ m) : n * k ≤ m * k :=
  Nat.mul_comm k m ▸ Nat.mul_comm k n ▸ mul_le_mul_left k h

protected theorem mul_le_mul {n₁ m₁ n₂ m₂ : Nat} (h₁ : n₁ ≤ n₂) (h₂ : m₁ ≤ m₂) : n₁ * m₁ ≤ n₂ * m₂ :=
  Nat.le_trans (mul_le_mul_right _ h₁) (mul_le_mul_left _ h₂)

protected theorem mul_lt_mul_of_pos_left {n m k : Nat} (h : n < m) (hk : k > 0) : k * n < k * m :=
  Nat.lt_of_lt_of_le (Nat.add_lt_add_left hk _) (Nat.mul_succ k n ▸ Nat.mul_le_mul_left k (succ_le_of_lt h))

protected theorem mul_lt_mul_of_pos_right {n m k : Nat} (h : n < m) (hk : k > 0) : n * k < m * k :=
  Nat.mul_comm k m ▸ Nat.mul_comm k n ▸ Nat.mul_lt_mul_of_pos_left h hk

protected theorem mul_pos {n m : Nat} (ha : n > 0) (hb : m > 0) : n * m > 0 :=
  have h : 0 * m < n * m := Nat.mul_lt_mul_of_pos_right ha hb
  Nat.zero_mul m ▸ h

protected theorem le_of_mul_le_mul_left {a b c : Nat} (h : c * a ≤ c * b) (hc : 0 < c) : a ≤ b :=
  Nat.ge_of_not_lt fun hlt : b < a =>
    have h' : c * b < c * a := Nat.mul_lt_mul_of_pos_left hlt hc
    absurd h (Nat.not_le_of_gt h')

protected theorem eq_of_mul_eq_mul_left {m k n : Nat} (hn : 0 < n) (h : n * m = n * k) : m = k :=
  Nat.le_antisymm (Nat.le_of_mul_le_mul_left (Nat.le_of_eq h) hn)
                  (Nat.le_of_mul_le_mul_left (Nat.le_of_eq h.symm) hn)

theorem eq_of_mul_eq_mul_right {n m k : Nat} (hm : 0 < m) (h : n * m = k * m) : n = k := by
  rw [Nat.mul_comm n m, Nat.mul_comm k m] at h; exact Nat.eq_of_mul_eq_mul_left hm h

/-! # power -/

theorem pow_succ (n m : Nat) : n^(succ m) = n^m * n :=
  rfl

theorem pow_zero (n : Nat) : n^0 = 1 := rfl

theorem pow_le_pow_of_le_left {n m : Nat} (h : n ≤ m) : ∀ (i : Nat), n^i ≤ m^i
  | 0      => Nat.le_refl _
  | succ i => Nat.mul_le_mul (pow_le_pow_of_le_left h i) h

theorem pow_le_pow_of_le_right {n : Nat} (hx : n > 0) {i : Nat} : ∀ {j}, i ≤ j → n^i ≤ n^j
  | 0,      h =>
    have : i = 0 := eq_zero_of_le_zero h
    this.symm ▸ Nat.le_refl _
  | succ j, h =>
    match le_or_eq_of_le_succ h with
    | Or.inl h => show n^i ≤ n^j * n from
      have : n^i * 1 ≤ n^j * n := Nat.mul_le_mul (pow_le_pow_of_le_right hx h) hx
      Nat.mul_one (n^i) ▸ this
    | Or.inr h =>
      h.symm ▸ Nat.le_refl _

theorem pos_pow_of_pos {n : Nat} (m : Nat) (h : 0 < n) : 0 < n^m :=
  pow_le_pow_of_le_right h (Nat.zero_le _)

/-! # min/max -/

/--
`Nat.min a b` is the minimum of `a` and `b`:
* if `a ≤ b` then `Nat.min a b = a`
* if `b ≤ a` then `Nat.min a b = b`
-/
protected abbrev min (n m : Nat) := min n m

protected theorem min_def {n m : Nat} : min n m = if n ≤ m then n else m := rfl

instance : Max Nat := maxOfLe

/--
`Nat.max a b` is the maximum of `a` and `b`:
* if `a ≤ b` then `Nat.max a b = b`
* if `b ≤ a` then `Nat.max a b = a`
-/
protected abbrev max (n m : Nat) := max n m

protected theorem max_def {n m : Nat} : max n m = if n ≤ m then m else n := rfl


/-! # Auxiliary theorems for well-founded recursion -/

theorem not_eq_zero_of_lt (h : b < a) : a ≠ 0 := by
  cases a
  exact absurd h (Nat.not_lt_zero _)
  apply Nat.noConfusion

theorem pred_lt' {n m : Nat} (h : m < n) : pred n < n :=
  pred_lt (not_eq_zero_of_lt h)

/-! # sub/pred theorems -/

theorem add_sub_self_left (a b : Nat) : (a + b) - a = b := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Nat.succ_add, Nat.succ_sub_succ]
    apply ih

theorem add_sub_self_right (a b : Nat) : (a + b) - b = a := by
  rw [Nat.add_comm]; apply add_sub_self_left

theorem sub_le_succ_sub (a i : Nat) : a - i ≤ a.succ - i := by
  cases i with
  | zero => apply Nat.le_of_lt; apply Nat.lt_succ_self
  | succ i => rw [Nat.sub_succ, Nat.succ_sub_succ]; apply Nat.pred_le

theorem zero_lt_sub_of_lt (h : i < a) : 0 < a - i := by
  induction a with
  | zero => contradiction
  | succ a ih =>
    match Nat.eq_or_lt_of_le h with
    | Or.inl h => injection h with h; subst h; rw [←Nat.add_one, Nat.add_sub_self_left]; decide
    | Or.inr h =>
      have : 0 < a - i := ih (Nat.lt_of_succ_lt_succ h)
      exact Nat.lt_of_lt_of_le this (Nat.sub_le_succ_sub _ _)

theorem sub_succ_lt_self (a i : Nat) (h : i < a) : a - (i + 1) < a - i := by
  rw [Nat.add_succ, Nat.sub_succ]
  apply Nat.pred_lt
  apply Nat.not_eq_zero_of_lt
  apply Nat.zero_lt_sub_of_lt
  assumption

theorem succ_pred {a : Nat} (h : a ≠ 0) : a.pred.succ = a := by
  induction a with
  | zero => contradiction
  | succ => rfl

theorem sub_ne_zero_of_lt : {a b : Nat} → a < b → b - a ≠ 0
  | 0, 0, h      => absurd h (Nat.lt_irrefl 0)
  | 0, succ b, _ => by simp
  | succ a, 0, h => absurd h (Nat.not_lt_zero a.succ)
  | succ a, succ b, h => by rw [Nat.succ_sub_succ]; exact sub_ne_zero_of_lt (Nat.lt_of_succ_lt_succ h)

theorem add_sub_of_le {a b : Nat} (h : a ≤ b) : a + (b - a) = b := by
  induction a with
  | zero => simp
  | succ a ih =>
    have hne : b - a ≠ 0 := Nat.sub_ne_zero_of_lt h
    have : a ≤ b := Nat.le_of_succ_le h
    rw [sub_succ, Nat.succ_add, ← Nat.add_succ, Nat.succ_pred hne, ih this]

protected theorem sub_add_cancel {n m : Nat} (h : m ≤ n) : n - m + m = n := by
  rw [Nat.add_comm, Nat.add_sub_of_le h]

protected theorem add_sub_add_right (n k m : Nat) : (n + k) - (m + k) = n - m := by
  induction k with
  | zero => simp
  | succ k ih => simp [add_succ, add_succ, succ_sub_succ, ih]

protected theorem add_sub_add_left (k n m : Nat) : (k + n) - (k + m) = n - m := by
  rw [Nat.add_comm k n, Nat.add_comm k m, Nat.add_sub_add_right]

protected theorem add_sub_cancel (n m : Nat) : n + m - m = n :=
  suffices n + m - (0 + m) = n by rw [Nat.zero_add] at this; assumption
  by rw [Nat.add_sub_add_right, Nat.sub_zero]

protected theorem add_sub_cancel_left (n m : Nat) : n + m - n = m :=
  show n + m - (n + 0) = m from
  by rw [Nat.add_sub_add_left, Nat.sub_zero]

protected theorem add_sub_assoc {m k : Nat} (h : k ≤ m) (n : Nat) : n + m - k = n + (m - k) := by
 cases Nat.le.dest h
 rename_i l hl
 rw [← hl, Nat.add_sub_cancel_left, Nat.add_comm k, ← Nat.add_assoc, Nat.add_sub_cancel]

protected theorem eq_add_of_sub_eq {a b c : Nat} (hle : b ≤ a) (h : a - b = c) : a = c + b := by
  rw [h.symm, Nat.sub_add_cancel hle]

protected theorem sub_eq_of_eq_add {a b c : Nat} (h : a = c + b) : a - b = c := by
  rw [h, Nat.add_sub_cancel]

theorem le_add_of_sub_le {a b c : Nat} (h : a - b ≤ c) : a ≤ c + b := by
  match le.dest h, Nat.le_total a b with
  | _, Or.inl hle =>
    exact Nat.le_trans hle (Nat.le_add_left ..)
  | ⟨d, hd⟩, Or.inr hge =>
    apply @le.intro _ _ d
    rw [Nat.add_comm, ← Nat.add_sub_assoc hge] at hd
    have hd := Nat.eq_add_of_sub_eq (Nat.le_trans hge (Nat.le_add_left ..)) hd
    rw [Nat.add_comm, hd]

protected theorem sub_lt_sub_left : ∀ {k m n : Nat}, k < m → k < n → m - n < m - k
  | 0, m+1, n+1, _, _ => by rw [Nat.add_sub_add_right]; exact lt_succ_of_le (Nat.sub_le _ _)
  | k+1, m+1, n+1, h1, h2 => by
    rw [Nat.add_sub_add_right, Nat.add_sub_add_right]
    exact Nat.sub_lt_sub_left (Nat.lt_of_succ_lt_succ h1) (Nat.lt_of_succ_lt_succ h2)

@[simp] protected theorem zero_sub (n : Nat) : 0 - n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [ih, Nat.sub_succ]; decide

protected theorem sub_self_add (n m : Nat) : n - (n + m) = 0 := by
  show (n + 0) - (n + m) = 0
  rw [Nat.add_sub_add_left, Nat.zero_sub]

protected theorem sub_eq_zero_of_le {n m : Nat} (h : n ≤ m) : n - m = 0 := by
  match le.dest h with
  | ⟨k, hk⟩ => rw [← hk, Nat.sub_self_add]

theorem sub_le_of_le_add {a b c : Nat} (h : a ≤ c + b) : a - b ≤ c := by
  match le.dest h, Nat.le_total a b with
  | _, Or.inl hle =>
    rw [Nat.sub_eq_zero_of_le hle]
    apply Nat.zero_le
  | ⟨d, hd⟩, Or.inr hge =>
    apply @le.intro _ _ d
    have hd := Nat.sub_eq_of_eq_add hd
    rw [Nat.add_comm, ← Nat.add_sub_assoc hge, Nat.add_comm]
    exact hd

theorem add_le_of_le_sub {a b c : Nat} (hle : b ≤ c) (h : a ≤ c - b) : a + b ≤ c := by
  match le.dest h with
  | ⟨d, hd⟩ =>
    apply @le.intro _ _ d
    rw [Nat.eq_add_of_sub_eq hle hd.symm]
    simp [Nat.add_comm, Nat.add_assoc, Nat.add_left_comm]

theorem le_sub_of_add_le {a b c : Nat} (h : a + b ≤ c) : a ≤ c - b := by
  match le.dest h with
  | ⟨d, hd⟩ =>
    apply @le.intro _ _ d
    have hd : a + d + b = c := by simp [← hd, Nat.add_comm, Nat.add_assoc, Nat.add_left_comm]
    have hd := Nat.sub_eq_of_eq_add hd.symm
    exact hd.symm

theorem add_lt_of_lt_sub {a b c : Nat} (h : a < c - b) : a + b < c := by
  have hle : b ≤ c := by
    apply Nat.ge_of_not_lt
    intro hgt
    apply Nat.not_lt_zero a
    rw [Nat.sub_eq_zero_of_le (Nat.le_of_lt hgt)] at h
    exact h
  have : a.succ + b ≤ c := add_le_of_le_sub hle h
  simp [Nat.succ_add] at this
  exact this

theorem lt_sub_of_add_lt {a b c : Nat} (h : a + b < c) : a < c - b :=
  have : a.succ + b ≤ c := by simp [Nat.succ_add]; exact h
  le_sub_of_add_le this

@[simp] protected theorem pred_zero : pred 0 = 0 :=
  rfl

@[simp] protected theorem pred_succ (n : Nat) : pred n.succ = n :=
  rfl

theorem sub.elim {motive : Nat → Prop}
    (x y : Nat)
    (h₁ : y ≤ x → (k : Nat) → x = y + k → motive k)
    (h₂ : x < y → motive 0)
    : motive (x - y) := by
  cases Nat.lt_or_ge x y with
  | inl hlt => rw [Nat.sub_eq_zero_of_le (Nat.le_of_lt hlt)]; exact h₂ hlt
  | inr hle => exact h₁ hle (x - y) (Nat.add_sub_of_le hle).symm

theorem mul_pred_left (n m : Nat) : pred n * m = n * m - m := by
  cases n with
  | zero   => simp
  | succ n => rw [Nat.pred_succ, succ_mul, Nat.add_sub_cancel]

theorem mul_pred_right (n m : Nat) : n * pred m = n * m - n := by
  rw [Nat.mul_comm, mul_pred_left, Nat.mul_comm]

protected theorem sub_sub (n m k : Nat) : n - m - k = n - (m + k) := by
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.add_succ, Nat.sub_succ, Nat.sub_succ, ih]

protected theorem mul_sub_right_distrib (n m k : Nat) : (n - m) * k = n * k - m * k := by
  induction m with
  | zero => simp
  | succ m ih => rw [Nat.sub_succ, Nat.mul_pred_left, ih, succ_mul, Nat.sub_sub]; done

protected theorem mul_sub_left_distrib (n m k : Nat) : n * (m - k) = n * m - n * k := by
  rw [Nat.mul_comm, Nat.mul_sub_right_distrib, Nat.mul_comm m n, Nat.mul_comm n k]

/-! # Helper normalization theorems -/

theorem not_le_eq (a b : Nat) : (¬ (a ≤ b)) = (b + 1 ≤ a) :=
  propext <| Iff.intro (fun h => Nat.gt_of_not_le h) (fun h => Nat.not_le_of_gt h)

theorem not_ge_eq (a b : Nat) : (¬ (a ≥ b)) = (a + 1 ≤ b) :=
  not_le_eq b a

theorem not_lt_eq (a b : Nat) : (¬ (a < b)) = (b ≤ a) :=
  propext <| Iff.intro (fun h => have h := Nat.succ_le_of_lt (Nat.gt_of_not_le h); Nat.le_of_succ_le_succ h) (fun h => Nat.not_le_of_gt (Nat.succ_le_succ h))

theorem not_gt_eq (a b : Nat) : (¬ (a > b)) = (a ≤ b) :=
  not_lt_eq b a

/-! # csimp theorems -/

@[csimp] theorem fold_eq_foldTR : @fold = @foldTR :=
  funext fun α => funext fun f => funext fun n => funext fun init =>
  let rec go : ∀ m n, foldTR.loop f (m + n) m (fold f n init) = fold f (m + n) init
    | 0,      n => by simp [foldTR.loop]
    | succ m, n => by rw [foldTR.loop, add_sub_self_left, succ_add]; exact go m (succ n)
  (go n 0).symm

@[csimp] theorem any_eq_anyTR : @any = @anyTR :=
  funext fun f => funext fun n =>
  let rec go : ∀ m n,  (any f n || anyTR.loop f (m + n) m) = any f (m + n)
    | 0,      n => by simp [anyTR.loop]
    | succ m, n => by
      rw [anyTR.loop, add_sub_self_left, ← Bool.or_assoc, succ_add]
      exact go m (succ n)
  (go n 0).symm

@[csimp] theorem all_eq_allTR : @all = @allTR :=
  funext fun f => funext fun n =>
  let rec go : ∀ m n,  (all f n && allTR.loop f (m + n) m) = all f (m + n)
    | 0,      n => by simp [allTR.loop]
    | succ m, n => by
      rw [allTR.loop, add_sub_self_left, ← Bool.and_assoc, succ_add]
      exact go m (succ n)
  (go n 0).symm

@[csimp] theorem repeat_eq_repeatTR : @repeat = @repeatTR :=
  funext fun α => funext fun f => funext fun n => funext fun init =>
  let rec go : ∀ m n, repeatTR.loop f m (repeat f n init) = repeat f (m + n) init
    | 0,      n => by simp [repeatTR.loop]
    | succ m, n => by rw [repeatTR.loop, succ_add]; exact go m (succ n)
  (go n 0).symm

end Nat

namespace Prod

/--
`(start, stop).foldI f a` evaluates `f` on all the numbers
from `start` (inclusive) to `stop` (exclusive) in increasing order:
* `(5, 8).foldI f init = init |> f 5 |> f 6 |> f 7`
-/
@[inline] def foldI {α : Type u} (f : Nat → α → α) (i : Nat × Nat) (a : α) : α :=
  Nat.foldTR.loop f i.2 (i.2 - i.1) a

/--
`(start, stop).anyI f a` returns true if `f` is true for some natural number
from `start` (inclusive) to `stop` (exclusive):
* `(5, 8).anyI f = f 5 || f 6 || f 7`
-/
@[inline] def anyI (f : Nat → Bool) (i : Nat × Nat) : Bool :=
  Nat.anyTR.loop f i.2 (i.2 - i.1)

/--
`(start, stop).allI f a` returns true if `f` is true for all natural numbers
from `start` (inclusive) to `stop` (exclusive):
* `(5, 8).anyI f = f 5 && f 6 && f 7`
-/
@[inline] def allI (f : Nat → Bool) (i : Nat × Nat) : Bool :=
  Nat.allTR.loop f i.2 (i.2 - i.1)

end Prod
