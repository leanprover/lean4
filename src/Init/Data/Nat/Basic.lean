/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura
-/
prelude
import Init.SimpLemmas
import Init.Data.NeZero

set_option linter.missingDocs true -- keep it documented
universe u

namespace Nat

/-- Compiled version of `Nat.rec` so that we can define `Nat.recAux` to be defeq to `Nat.rec`.
This is working around the fact that the compiler does not currently support recursors. -/
private def recCompiled {motive : Nat → Sort u} (zero : motive zero) (succ : (n : Nat) → motive n → motive (Nat.succ n)) : (t : Nat) → motive t
  | .zero => zero
  | .succ n => succ n (recCompiled zero succ n)

@[csimp]
private theorem rec_eq_recCompiled : @Nat.rec = @Nat.recCompiled :=
  funext fun _ => funext fun _ => funext fun succ => funext fun t =>
    Nat.recOn t rfl (fun n ih => congrArg (succ n) ih)

/-- Recursor identical to `Nat.rec` but uses notations `0` for `Nat.zero` and `· + 1` for `Nat.succ`.
Used as the default `Nat` eliminator by the `induction` tactic. -/
@[elab_as_elim, induction_eliminator]
protected abbrev recAux {motive : Nat → Sort u} (zero : motive 0) (succ : (n : Nat) → motive n → motive (n + 1)) (t : Nat) : motive t :=
  Nat.rec zero succ t

/-- Recursor identical to `Nat.casesOn` but uses notations `0` for `Nat.zero` and `· + 1` for `Nat.succ`.
Used as the default `Nat` eliminator by the `cases` tactic. -/
@[elab_as_elim, cases_eliminator]
protected abbrev casesAuxOn {motive : Nat → Sort u} (t : Nat) (zero : motive 0) (succ : (n : Nat) → motive (n + 1)) : motive t :=
  Nat.casesOn t zero succ


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
attribute [simp] Nat.not_lt_zero

theorem and_forall_add_one {p : Nat → Prop} : p 0 ∧ (∀ n, p (n + 1)) ↔ ∀ n, p n :=
  ⟨fun h n => Nat.casesOn n h.1 h.2, fun h => ⟨h _, fun _ => h _⟩⟩

theorem or_exists_add_one : p 0 ∨ (Exists fun n => p (n + 1)) ↔ Exists p :=
  ⟨fun h => h.elim (fun h0 => ⟨0, h0⟩) fun ⟨n, hn⟩ => ⟨n + 1, hn⟩,
    fun ⟨n, h⟩ => match n with | 0 => Or.inl h | n+1 => Or.inr ⟨n, h⟩⟩

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
  eq_of_beq h := by simpa using h
  rfl := by simp [BEq.beq]

theorem beq_eq_true_eq (a b : Nat) : ((a == b) = true) = (a = b) := by simp
theorem not_beq_eq_true_eq (a b : Nat) : ((!(a == b)) = true) = ¬(a = b) := by simp

/-! # Nat.add theorems -/

@[simp] protected theorem zero_add : ∀ (n : Nat), 0 + n = n
  | 0   => rfl
  | n+1 => congrArg succ (Nat.zero_add n)
instance : Std.LawfulIdentity (α := Nat) (· + ·) 0 where
  left_id := Nat.zero_add
  right_id := Nat.add_zero

theorem succ_add : ∀ (n m : Nat), (succ n) + m = succ (n + m)
  | _, 0   => rfl
  | n, m+1 => congrArg succ (succ_add n m)

theorem add_succ (n m : Nat) : n + succ m = succ (n + m) :=
  rfl

theorem add_one (n : Nat) : n + 1 = succ n :=
  rfl

@[simp] theorem succ_eq_add_one (n : Nat) : succ n = n + 1 :=
  rfl

@[simp] theorem add_one_ne_zero (n : Nat) : n + 1 ≠ 0 := nofun
theorem zero_ne_add_one (n : Nat) : 0 ≠ n + 1 := by simp

protected theorem add_comm : ∀ (n m : Nat), n + m = m + n
  | n, 0   => Eq.symm (Nat.zero_add n)
  | n, m+1 => by
    have : succ (n + m) = succ (m + n) := by apply congrArg; apply Nat.add_comm
    rw [succ_add m n]
    apply this
instance : Std.Commutative (α := Nat) (· + ·) := ⟨Nat.add_comm⟩

protected theorem add_assoc : ∀ (n m k : Nat), (n + m) + k = n + (m + k)
  | _, _, 0      => rfl
  | n, m, succ k => congrArg succ (Nat.add_assoc n m k)
instance : Std.Associative (α := Nat) (· + ·) := ⟨Nat.add_assoc⟩

protected theorem add_left_comm (n m k : Nat) : n + (m + k) = m + (n + k) := by
  rw [← Nat.add_assoc, Nat.add_comm n m, Nat.add_assoc]

protected theorem add_right_comm (n m k : Nat) : (n + m) + k = (n + k) + m := by
  rw [Nat.add_assoc, Nat.add_comm m k, ← Nat.add_assoc]

protected theorem add_left_cancel {n m k : Nat} : n + m = n + k → m = k := by
  induction n with
  | zero => simp
  | succ n ih => simp [succ_add, succ.injEq]; intro h; apply ih h

protected theorem add_right_cancel {n m k : Nat} (h : n + m = k + m) : n = k := by
  rw [Nat.add_comm n m, Nat.add_comm k m] at h
  apply Nat.add_left_cancel h

theorem eq_zero_of_add_eq_zero : ∀ {n m}, n + m = 0 → n = 0 ∧ m = 0
  | 0, 0, _ => ⟨rfl, rfl⟩
  | _+1, 0, h => Nat.noConfusion h

protected theorem eq_zero_of_add_eq_zero_left (h : n + m = 0) : m = 0 :=
  (Nat.eq_zero_of_add_eq_zero h).2

/-! # Nat.mul theorems -/

@[simp] protected theorem mul_zero (n : Nat) : n * 0 = 0 :=
  rfl

theorem mul_succ (n m : Nat) : n * succ m = n * m + n :=
  rfl

theorem mul_add_one (n m : Nat) : n * (m + 1) = n * m + n :=
  rfl

@[simp] protected theorem zero_mul : ∀ (n : Nat), 0 * n = 0
  | 0      => rfl
  | succ n => mul_succ 0 n ▸ (Nat.zero_mul n).symm ▸ rfl

theorem succ_mul (n m : Nat) : (succ n) * m = (n * m) + m := by
  induction m with
  | zero => rfl
  | succ m ih => rw [mul_succ, add_succ, ih, mul_succ, add_succ, Nat.add_right_comm]

theorem add_one_mul (n m : Nat) : (n + 1) * m = (n * m) + m := succ_mul n m

protected theorem mul_comm : ∀ (n m : Nat), n * m = m * n
  | n, 0      => (Nat.zero_mul n).symm ▸ (Nat.mul_zero n).symm ▸ rfl
  | n, succ m => (mul_succ n m).symm ▸ (succ_mul m n).symm ▸ (Nat.mul_comm n m).symm ▸ rfl
instance : Std.Commutative (α := Nat) (· * ·) := ⟨Nat.mul_comm⟩

@[simp] protected theorem mul_one : ∀ (n : Nat), n * 1 = n :=
  Nat.zero_add

@[simp] protected theorem one_mul (n : Nat) : 1 * n = n :=
  Nat.mul_comm n 1 ▸ Nat.mul_one n
instance : Std.LawfulIdentity (α := Nat) (· * ·) 1 where
  left_id := Nat.one_mul
  right_id := Nat.mul_one

protected theorem left_distrib (n m k : Nat) : n * (m + k) = n * m + n * k := by
  induction n with
  | zero      => repeat rw [Nat.zero_mul]
  | succ n ih => simp [succ_mul, ih]; rw [Nat.add_assoc, Nat.add_assoc (n*m)]; apply congrArg; apply Nat.add_left_comm

protected theorem right_distrib (n m k : Nat) : (n + m) * k = n * k + m * k := by
  rw [Nat.mul_comm, Nat.left_distrib]; simp [Nat.mul_comm]

protected theorem mul_add (n m k : Nat) : n * (m + k) = n * m + n * k :=
  Nat.left_distrib n m k

protected theorem add_mul (n m k : Nat) : (n + m) * k = n * k + m * k :=
  Nat.right_distrib n m k

protected theorem mul_assoc : ∀ (n m k : Nat), (n * m) * k = n * (m * k)
  | _, _, 0      => rfl
  | n, m, succ k => by simp [mul_succ, Nat.mul_assoc n m k, Nat.left_distrib]
instance : Std.Associative (α := Nat) (· * ·) := ⟨Nat.mul_assoc⟩

protected theorem mul_left_comm (n m k : Nat) : n * (m * k) = m * (n * k) := by
  rw [← Nat.mul_assoc, Nat.mul_comm n m, Nat.mul_assoc]

protected theorem mul_two (n) : n * 2 = n + n := by rw [Nat.mul_succ, Nat.mul_one]
protected theorem two_mul (n) : 2 * n = n + n := by rw [Nat.succ_mul, Nat.one_mul]

/-! # Inequalities -/

attribute [simp] Nat.le_refl

theorem succ_lt_succ {n m : Nat} : n < m → succ n < succ m := succ_le_succ

theorem lt_succ_of_le {n m : Nat} : n ≤ m → n < succ m := succ_le_succ

theorem le_of_lt_add_one {n m : Nat} : n < m + 1 → n ≤ m := le_of_succ_le_succ

theorem lt_add_one_of_le {n m : Nat} : n ≤ m → n < m + 1 := succ_le_succ

@[simp] protected theorem sub_zero (n : Nat) : n - 0 = n := rfl

theorem not_add_one_le_zero (n : Nat) : ¬ n + 1 ≤ 0 := nofun

theorem not_add_one_le_self : (n : Nat) → ¬ n + 1 ≤ n := Nat.not_succ_le_self

theorem add_one_pos (n : Nat) : 0 < n + 1 := Nat.zero_lt_succ n

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

theorem sub_one_lt : ∀ {n : Nat}, n ≠ 0 → n - 1 < n := pred_lt

@[simp] theorem sub_le (n m : Nat) : n - m ≤ n := by
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

theorem sub_succ (n m : Nat) : n - succ m = pred (n - m) := rfl

theorem succ_sub_succ (n m : Nat) : succ n - succ m = n - m :=
  succ_sub_succ_eq_sub n m

@[simp] protected theorem sub_self : ∀ (n : Nat), n - n = 0
  | 0        => by rw [Nat.sub_zero]
  | (succ n) => by rw [succ_sub_succ, Nat.sub_self n]

theorem sub_add_eq (a b c : Nat) : a - (b + c) = a - b - c := by
  induction c with
  | zero => simp
  | succ c ih => simp only [Nat.add_succ, Nat.sub_succ, ih]

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

theorem lt.step {n m : Nat} : n < m → n < succ m := le_step

theorem le_of_succ_le {n m : Nat} (h : succ n ≤ m) : n ≤ m := Nat.le_trans (le_succ n) h
theorem lt_of_succ_lt      {n m : Nat} : succ n < m → n < m := le_of_succ_le
protected theorem le_of_lt {n m : Nat} : n < m → n ≤ m := le_of_succ_le

theorem lt_of_succ_lt_succ {n m : Nat} : succ n < succ m → n < m := le_of_succ_le_succ

theorem lt_of_succ_le {n m : Nat} (h : succ n ≤ m) : n < m := h
theorem succ_le_of_lt {n m : Nat} (h : n < m) : succ n ≤ m := h

theorem eq_zero_or_pos : ∀ (n : Nat), n = 0 ∨ n > 0
  | 0   => Or.inl rfl
  | _+1 => Or.inr (succ_pos _)

protected theorem pos_of_ne_zero {n : Nat} : n ≠ 0 → 0 < n := (eq_zero_or_pos n).resolve_left

theorem pos_of_neZero (n : Nat) [NeZero n] : 0 < n := Nat.pos_of_ne_zero (NeZero.ne _)

theorem lt.base (n : Nat) : n < succ n := Nat.le_refl (succ n)

theorem lt_succ_self (n : Nat) : n < succ n := lt.base n

@[simp] protected theorem lt_add_one (n : Nat) : n < n + 1 := lt.base n

protected theorem le_total (m n : Nat) : m ≤ n ∨ n ≤ m :=
  match Nat.lt_or_ge m n with
  | Or.inl h => Or.inl (Nat.le_of_lt h)
  | Or.inr h => Or.inr h

theorem eq_zero_of_le_zero {n : Nat} (h : n ≤ 0) : n = 0 := Nat.le_antisymm h (zero_le _)

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

theorem ne_of_lt {a b : Nat} (h : a < b) : a ≠ b := fun he => absurd (he ▸ h) (Nat.lt_irrefl a)

theorem le_or_eq_of_le_succ {m n : Nat} (h : m ≤ succ n) : m ≤ n ∨ m = succ n :=
  Decidable.byCases
    (fun (h' : m = succ n) => Or.inr h')
    (fun (h' : m ≠ succ n) =>
       have : m < succ n := Nat.lt_of_le_of_ne h h'
       have : succ m ≤ succ n := succ_le_of_lt this
       Or.inl (le_of_succ_le_succ this))

theorem le_or_eq_of_le_add_one {m n : Nat} (h : m ≤ n + 1) : m ≤ n ∨ m = n + 1 :=
  le_or_eq_of_le_succ h

@[simp] theorem le_add_right : ∀ (n k : Nat), n ≤ n + k
  | n, 0   => Nat.le_refl n
  | n, k+1 => le_succ_of_le (le_add_right n k)

@[simp] theorem le_add_left (n m : Nat): n ≤ m + n :=
  Nat.add_comm n m ▸ le_add_right n m

theorem le_of_add_right_le {n m k : Nat} (h : n + k ≤ m) : n ≤ m :=
  Nat.le_trans (le_add_right n k) h

theorem le_add_right_of_le {n m k : Nat} (h : n ≤ m) : n ≤ m + k :=
  Nat.le_trans h (le_add_right m k)

theorem lt_of_add_one_le {n m : Nat} (h : n + 1 ≤ m) : n < m := h

theorem add_one_le_of_lt {n m : Nat} (h : n < m) : n + 1 ≤ m := h

protected theorem lt_add_left (c : Nat) (h : a < b) : a < c + b :=
  Nat.lt_of_lt_of_le h (Nat.le_add_left ..)

protected theorem lt_add_right (c : Nat) (h : a < b) : a < b + c :=
  Nat.lt_of_lt_of_le h (Nat.le_add_right ..)

theorem lt_of_add_right_lt {n m k : Nat} (h : n + k < m) : n < m :=
  Nat.lt_of_le_of_lt (Nat.le_add_right ..) h

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
protected theorem not_le_of_lt : ∀{a b : Nat}, a < b → ¬(b ≤ a) := Nat.not_le_of_gt
protected theorem not_lt_of_ge : ∀{a b : Nat}, b ≥ a → ¬(b < a) := flip Nat.not_le_of_gt
protected theorem not_lt_of_le : ∀{a b : Nat}, a ≤ b → ¬(b < a) := flip Nat.not_le_of_gt
protected theorem lt_le_asymm : ∀{a b : Nat}, a < b → ¬(b ≤ a) := Nat.not_le_of_gt
protected theorem le_lt_asymm : ∀{a b : Nat}, a ≤ b → ¬(b < a) := flip Nat.not_le_of_gt

theorem gt_of_not_le {n m : Nat} (h : ¬ n ≤ m) : n > m := (Nat.lt_or_ge m n).resolve_right h
protected theorem lt_of_not_ge : ∀{a b : Nat}, ¬(b ≥ a) → b < a := Nat.gt_of_not_le
protected theorem lt_of_not_le : ∀{a b : Nat}, ¬(a ≤ b) → b < a := Nat.gt_of_not_le

theorem ge_of_not_lt {n m : Nat} (h : ¬ n < m) : n ≥ m := (Nat.lt_or_ge n m).resolve_left h
protected theorem le_of_not_gt : ∀{a b : Nat}, ¬(b > a) → b ≤ a := Nat.ge_of_not_lt
protected theorem le_of_not_lt : ∀{a b : Nat}, ¬(a < b) → b ≤ a := Nat.ge_of_not_lt

theorem ne_of_gt {a b : Nat} (h : b < a) : a ≠ b := (ne_of_lt h).symm
protected theorem ne_of_lt' : ∀{a b : Nat}, a < b → b ≠ a := ne_of_gt

@[simp] protected theorem not_le {a b : Nat} : ¬ a ≤ b ↔ b < a :=
  Iff.intro Nat.gt_of_not_le Nat.not_le_of_gt
@[simp] protected theorem not_lt {a b : Nat} : ¬ a < b ↔ b ≤ a :=
  Iff.intro Nat.ge_of_not_lt (flip Nat.not_le_of_gt)

protected theorem le_of_not_le {a b : Nat} (h : ¬ b ≤ a) : a ≤ b := Nat.le_of_lt (Nat.not_le.1 h)
protected theorem le_of_not_ge : ∀{a b : Nat}, ¬(a ≥ b) → a ≤ b:= @Nat.le_of_not_le

protected theorem lt_trichotomy (a b : Nat) : a < b ∨ a = b ∨ b < a :=
  match Nat.lt_or_ge a b with
  | .inl h => .inl h
  | .inr h =>
    match Nat.eq_or_lt_of_le h with
    | .inl h => .inr (.inl h.symm)
    | .inr h => .inr (.inr h)

protected theorem lt_or_gt_of_ne {a b : Nat} (ne : a ≠ b) : a < b ∨ a > b :=
  match Nat.lt_trichotomy a b with
  | .inl h => .inl h
  | .inr (.inl e) => False.elim (ne e)
  | .inr (.inr h) => .inr h

protected theorem lt_or_lt_of_ne : ∀{a b : Nat}, a ≠ b → a < b ∨ b < a := Nat.lt_or_gt_of_ne

protected theorem le_antisymm_iff {a b : Nat} : a = b ↔ a ≤ b ∧ b ≤ a :=
  Iff.intro (fun p => And.intro (Nat.le_of_eq p) (Nat.le_of_eq p.symm))
            (fun ⟨hle, hge⟩ => Nat.le_antisymm hle hge)
protected theorem eq_iff_le_and_ge : ∀{a b : Nat}, a = b ↔ a ≤ b ∧ b ≤ a := @Nat.le_antisymm_iff

instance : Std.Antisymm ( . ≤ . : Nat → Nat → Prop) where
  antisymm _ _ h₁ h₂ := Nat.le_antisymm h₁ h₂

instance : Std.Antisymm (¬ . < . : Nat → Nat → Prop) where
  antisymm _ _ h₁ h₂ := Nat.le_antisymm (Nat.ge_of_not_lt h₂) (Nat.ge_of_not_lt h₁)

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

protected theorem lt_add_of_pos_left (h : 0 < k) : n < k + n := by
  rw [Nat.add_comm]
  exact Nat.add_lt_add_left h n

protected theorem lt_add_of_pos_right (h : 0 < k) : n < n + k :=
  Nat.add_lt_add_left h n

protected theorem zero_lt_one : 0 < (1:Nat) :=
  zero_lt_succ 0

protected theorem pos_iff_ne_zero : 0 < n ↔ n ≠ 0 := ⟨ne_of_gt, Nat.pos_of_ne_zero⟩

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

@[simp] protected theorem add_le_add_iff_right {n : Nat} : m + n ≤ k + n ↔ m ≤ k :=
  ⟨Nat.le_of_add_le_add_right, fun h => Nat.add_le_add_right h _⟩

/-! ### le/lt -/

protected theorem lt_asymm {a b : Nat} (h : a < b) : ¬ b < a := Nat.not_lt.2 (Nat.le_of_lt h)
/-- Alias for `Nat.lt_asymm`. -/
protected abbrev not_lt_of_gt := @Nat.lt_asymm
/-- Alias for `Nat.lt_asymm`. -/
protected abbrev not_lt_of_lt := @Nat.lt_asymm

protected theorem lt_iff_le_not_le {m n : Nat} : m < n ↔ m ≤ n ∧ ¬ n ≤ m :=
  ⟨fun h => ⟨Nat.le_of_lt h, Nat.not_le_of_gt h⟩, fun ⟨_, h⟩ => Nat.lt_of_not_ge h⟩
/-- Alias for `Nat.lt_iff_le_not_le`. -/
protected abbrev lt_iff_le_and_not_ge := @Nat.lt_iff_le_not_le

protected theorem lt_iff_le_and_ne {m n : Nat} : m < n ↔ m ≤ n ∧ m ≠ n :=
  ⟨fun h => ⟨Nat.le_of_lt h, Nat.ne_of_lt h⟩, fun h => Nat.lt_of_le_of_ne h.1 h.2⟩

protected theorem ne_iff_lt_or_gt {a b : Nat} : a ≠ b ↔ a < b ∨ b < a :=
  ⟨Nat.lt_or_gt_of_ne, fun | .inl h => Nat.ne_of_lt h | .inr h => Nat.ne_of_gt h⟩
/-- Alias for `Nat.ne_iff_lt_or_gt`. -/
protected abbrev lt_or_gt := @Nat.ne_iff_lt_or_gt

/-- Alias for `Nat.le_total`. -/
protected abbrev le_or_ge := @Nat.le_total
/-- Alias for `Nat.le_total`. -/
protected abbrev le_or_le := @Nat.le_total

protected theorem eq_or_lt_of_not_lt {a b : Nat} (hnlt : ¬ a < b) : a = b ∨ b < a :=
  (Nat.lt_trichotomy ..).resolve_left hnlt

protected theorem lt_or_eq_of_le {n m : Nat} (h : n ≤ m) : n < m ∨ n = m :=
  (Nat.lt_or_ge ..).imp_right (Nat.le_antisymm h)

protected theorem le_iff_lt_or_eq {n m : Nat} : n ≤ m ↔ n < m ∨ n = m :=
  ⟨Nat.lt_or_eq_of_le, fun | .inl h => Nat.le_of_lt h | .inr rfl => Nat.le_refl _⟩

protected theorem lt_succ_iff : m < succ n ↔ m ≤ n := ⟨le_of_lt_succ, lt_succ_of_le⟩

protected theorem lt_add_one_iff : m < n + 1 ↔ m ≤ n := ⟨le_of_lt_succ, lt_succ_of_le⟩

protected theorem lt_succ_iff_lt_or_eq : m < succ n ↔ m < n ∨ m = n :=
  Nat.lt_succ_iff.trans Nat.le_iff_lt_or_eq

protected theorem lt_add_one_iff_lt_or_eq : m < n + 1 ↔ m < n ∨ m = n :=
  Nat.lt_add_one_iff.trans Nat.le_iff_lt_or_eq

protected theorem eq_of_lt_succ_of_not_lt (hmn : m < n + 1) (h : ¬ m < n) : m = n :=
  (Nat.lt_succ_iff_lt_or_eq.1 hmn).resolve_left h

protected theorem eq_of_le_of_lt_succ (h₁ : n ≤ m) (h₂ : m < n + 1) : m = n :=
  Nat.le_antisymm (le_of_succ_le_succ h₂) h₁


/-! ## zero/one/two -/

theorem le_zero : i ≤ 0 ↔ i = 0 := ⟨Nat.eq_zero_of_le_zero, fun | rfl => Nat.le_refl _⟩

/-- Alias for `Nat.zero_lt_one`. -/
protected abbrev one_pos := @Nat.zero_lt_one

protected theorem two_pos : 0 < 2 := Nat.zero_lt_succ _

protected theorem ne_zero_iff_zero_lt : n ≠ 0 ↔ 0 < n := Nat.pos_iff_ne_zero.symm

protected theorem zero_lt_two : 0 < 2 := Nat.zero_lt_succ _

protected theorem one_lt_two : 1 < 2 := Nat.succ_lt_succ Nat.zero_lt_one

protected theorem eq_zero_of_not_pos (h : ¬0 < n) : n = 0 :=
  Nat.eq_zero_of_le_zero (Nat.not_lt.1 h)

/-! ## succ/pred -/

attribute [simp] zero_lt_succ

theorem succ_ne_self (n) : succ n ≠ n := Nat.ne_of_gt (lt_succ_self n)

theorem add_one_ne_self (n) : n + 1 ≠ n := Nat.ne_of_gt (lt_succ_self n)

theorem succ_le : succ n ≤ m ↔ n < m := .rfl

theorem add_one_le_iff : n + 1 ≤ m ↔ n < m := .rfl

theorem lt_succ : m < succ n ↔ m ≤ n := ⟨le_of_lt_succ, lt_succ_of_le⟩

theorem lt_succ_of_lt (h : a < b) : a < succ b := le_succ_of_le h

theorem lt_add_one_of_lt (h : a < b) : a < b + 1 := le_succ_of_le h

@[simp] theorem lt_one_iff : n < 1 ↔ n = 0 := Nat.lt_succ_iff.trans <| by rw [le_zero_eq]

theorem succ_pred_eq_of_ne_zero : ∀ {n}, n ≠ 0 → succ (pred n) = n
  | _+1, _ => rfl

theorem eq_zero_or_eq_succ_pred : ∀ n, n = 0 ∨ n = succ (pred n)
  | 0 => .inl rfl
  | _+1 => .inr rfl

theorem succ_inj' : succ a = succ b ↔ a = b := (Nat.succ.injEq a b).to_iff

theorem succ_le_succ_iff : succ a ≤ succ b ↔ a ≤ b := ⟨le_of_succ_le_succ, succ_le_succ⟩

theorem succ_lt_succ_iff : succ a < succ b ↔ a < b := ⟨lt_of_succ_lt_succ, succ_lt_succ⟩

theorem add_one_inj : a + 1 = b + 1 ↔ a = b := succ_inj'

theorem ne_add_one (n : Nat) : n ≠ n + 1 := fun h => by cases h

theorem add_one_ne (n : Nat) : n + 1 ≠ n := fun h => by cases h

theorem add_one_le_add_one_iff : a + 1 ≤ b + 1 ↔ a ≤ b := succ_le_succ_iff

theorem add_one_lt_add_one_iff : a + 1 < b + 1 ↔ a < b := succ_lt_succ_iff

theorem pred_inj : ∀ {a b}, 0 < a → 0 < b → pred a = pred b → a = b
  | _+1, _+1, _, _ => congrArg _

theorem pred_ne_self : ∀ {a}, a ≠ 0 → pred a ≠ a
  | _+1, _ => (succ_ne_self _).symm

theorem sub_one_ne_self : ∀ {a}, a ≠ 0 → a - 1 ≠ a
  | _+1, _ => (succ_ne_self _).symm

theorem pred_lt_self : ∀ {a}, 0 < a → pred a < a
  | _+1, _ => lt_succ_self _

theorem pred_lt_pred : ∀ {n m}, n ≠ 0 → n < m → pred n < pred m
  | _+1, _+1, _, h => lt_of_succ_lt_succ h

theorem pred_le_iff_le_succ : ∀ {n m}, pred n ≤ m ↔ n ≤ succ m
  | 0, _ => ⟨fun _ => Nat.zero_le _, fun _ => Nat.zero_le _⟩
  | _+1, _ => Nat.succ_le_succ_iff.symm

theorem le_succ_of_pred_le : pred n ≤ m → n ≤ succ m := pred_le_iff_le_succ.1

theorem pred_le_of_le_succ : n ≤ succ m → pred n ≤ m := pred_le_iff_le_succ.2

theorem lt_pred_iff_succ_lt : ∀ {n m}, n < pred m ↔ succ n < m
  | _, 0 => ⟨nofun, nofun⟩
  | _, _+1 => Nat.succ_lt_succ_iff.symm

theorem succ_lt_of_lt_pred : n < pred m → succ n < m := lt_pred_iff_succ_lt.1

theorem lt_pred_of_succ_lt : succ n < m → n < pred m := lt_pred_iff_succ_lt.2

theorem le_pred_iff_lt : ∀ {n m}, 0 < m → (n ≤ pred m ↔ n < m)
  | 0, _+1, _ => ⟨fun _ => Nat.zero_lt_succ _, fun _ => Nat.zero_le _⟩
  | _+1, _+1, _ => Nat.lt_pred_iff_succ_lt

theorem le_pred_of_lt (h : n < m) : n ≤ pred m := (le_pred_iff_lt (Nat.zero_lt_of_lt h)).2 h

theorem le_sub_one_of_lt : a < b → a ≤ b - 1 := Nat.le_pred_of_lt

theorem lt_of_le_pred (h : 0 < m) : n ≤ pred m → n < m := (le_pred_iff_lt h).1

theorem lt_of_le_sub_one (h : 0 < m) : n ≤ m - 1 → n < m := (le_pred_iff_lt h).1

protected theorem le_sub_one_iff_lt (h : 0 < m) : n ≤ m - 1 ↔ n < m :=
  ⟨Nat.lt_of_le_sub_one h, Nat.le_sub_one_of_lt⟩

theorem exists_eq_succ_of_ne_zero : ∀ {n}, n ≠ 0 → Exists fun k => n = succ k
  | _+1, _ => ⟨_, rfl⟩

theorem exists_eq_add_one_of_ne_zero : ∀ {n}, n ≠ 0 → Exists fun k => n = k + 1
  | _+1, _ => ⟨_, rfl⟩

/-! # Basic theorems for comparing numerals -/

theorem ctor_eq_zero : Nat.zero = 0 :=
  rfl

protected theorem one_ne_zero : 1 ≠ (0 : Nat) :=
  fun h => Nat.noConfusion h

protected theorem zero_ne_one : 0 ≠ (1 : Nat) :=
  fun h => Nat.noConfusion h

theorem succ_ne_zero (n : Nat) : succ n ≠ 0 := by simp

instance instNeZeroSucc {n : Nat} : NeZero (n + 1) := ⟨succ_ne_zero n⟩

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

protected theorem pow_succ (n m : Nat) : n^(succ m) = n^m * n :=
  rfl

protected theorem pow_add_one (n m : Nat) : n^(m + 1) = n^m * n :=
  rfl

protected theorem pow_zero (n : Nat) : n^0 = 1 := rfl

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

@[simp] theorem zero_pow_of_pos (n : Nat) (h : 0 < n) : 0 ^ n = 0 := by
  cases n with
  | zero => cases h
  | succ n => simp [Nat.pow_succ]

protected theorem two_pow_pos (w : Nat) : 0 < 2^w := Nat.pos_pow_of_pos _ (by decide)

instance {n m : Nat} [NeZero n] : NeZero (n^m) :=
  ⟨Nat.ne_zero_iff_zero_lt.mpr (Nat.pos_pow_of_pos m (pos_of_neZero _))⟩

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

theorem pred_lt_of_lt {n m : Nat} (h : m < n) : pred n < n :=
  pred_lt (not_eq_zero_of_lt h)

set_option linter.missingDocs false in
@[deprecated pred_lt_of_lt (since := "2024-06-01")] abbrev pred_lt' := @pred_lt_of_lt

theorem sub_one_lt_of_lt {n m : Nat} (h : m < n) : n - 1 < n :=
  sub_one_lt (not_eq_zero_of_lt h)

/-! # pred theorems -/

protected theorem pred_zero : pred 0 = 0 := rfl
protected theorem pred_succ (n : Nat) : pred n.succ = n := rfl

@[simp] protected theorem zero_sub_one : 0 - 1 = 0 := rfl
@[simp] protected theorem add_one_sub_one (n : Nat) : n + 1 - 1 = n := rfl

theorem sub_one_eq_self {n : Nat} : n - 1 = n ↔ n = 0 := by cases n <;> simp [ne_add_one]
theorem eq_self_sub_one {n : Nat} : n = n - 1 ↔ n = 0 := by cases n <;> simp [add_one_ne]

theorem succ_pred {a : Nat} (h : a ≠ 0) : a.pred.succ = a := by
  induction a with
  | zero => contradiction
  | succ => rfl

theorem sub_one_add_one {a : Nat} (h : a ≠ 0) : a - 1 + 1 = a := by
  induction a with
  | zero => contradiction
  | succ => rfl

theorem succ_pred_eq_of_pos : ∀ {n}, 0 < n → succ (pred n) = n
  | _+1, _ => rfl

theorem sub_one_add_one_eq_of_pos : ∀ {n}, 0 < n → (n - 1) + 1 = n
  | _+1, _ => rfl

theorem eq_zero_or_eq_sub_one_add_one : ∀ {n}, n = 0 ∨ n = n - 1 + 1
  | 0 => Or.inl rfl
  | _+1 => Or.inr rfl

@[simp] theorem pred_eq_sub_one : pred n = n - 1 := rfl

/-! # sub theorems -/

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
    | Or.inl h => injection h with h; subst h; rw [Nat.add_sub_self_left]; decide
    | Or.inr h =>
      have : 0 < a - i := ih (Nat.lt_of_succ_lt_succ h)
      exact Nat.lt_of_lt_of_le this (Nat.sub_le_succ_sub _ _)

theorem sub_succ_lt_self (a i : Nat) (h : i < a) : a - (i + 1) < a - i := by
  rw [Nat.add_succ, Nat.sub_succ]
  apply Nat.pred_lt
  apply Nat.not_eq_zero_of_lt
  apply Nat.zero_lt_sub_of_lt
  assumption

theorem sub_ne_zero_of_lt : {a b : Nat} → a < b → b - a ≠ 0
  | 0, 0, h      => absurd h (Nat.lt_irrefl 0)
  | 0, succ b, _ => by simp only [Nat.sub_zero, ne_eq, not_false_eq_true, Nat.succ_ne_zero]
  | succ a, 0, h => absurd h (Nat.not_lt_zero a.succ)
  | succ a, succ b, h => by rw [Nat.succ_sub_succ]; exact sub_ne_zero_of_lt (Nat.lt_of_succ_lt_succ h)

theorem add_sub_of_le {a b : Nat} (h : a ≤ b) : a + (b - a) = b := by
  induction a with
  | zero => simp
  | succ a ih =>
    have hne : b - a ≠ 0 := Nat.sub_ne_zero_of_lt h
    have : a ≤ b := Nat.le_of_succ_le h
    rw [sub_succ, Nat.succ_add, ← Nat.add_succ, Nat.succ_pred hne, ih this]

theorem sub_one_cancel : ∀ {a b : Nat}, 0 < a → 0 < b → a - 1 = b - 1 → a = b
  | _+1, _+1, _, _ => congrArg _

@[simp] protected theorem sub_add_cancel {n m : Nat} (h : m ≤ n) : n - m + m = n := by
  rw [Nat.add_comm, Nat.add_sub_of_le h]

protected theorem add_sub_add_right (n k m : Nat) : (n + k) - (m + k) = n - m := by
  induction k with
  | zero => simp
  | succ k ih => simp [← Nat.add_assoc, succ_sub_succ_eq_sub, ih]

protected theorem add_sub_add_left (k n m : Nat) : (k + n) - (k + m) = n - m := by
  rw [Nat.add_comm k n, Nat.add_comm k m, Nat.add_sub_add_right]

@[simp] protected theorem add_sub_cancel (n m : Nat) : n + m - m = n :=
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

protected theorem sub_lt_sub_right : ∀ {a b c : Nat}, c ≤ a → a < b → a - c < b - c
  | 0, _, _, hle, h => by
    rw [Nat.eq_zero_of_le_zero hle, Nat.sub_zero, Nat.sub_zero]
    exact h
  | _, _, 0, _, h => by
    rw [Nat.sub_zero, Nat.sub_zero]
    exact h
  | _+1, _+1, _+1, hle, h => by
    rw [Nat.add_sub_add_right, Nat.add_sub_add_right]
    exact Nat.sub_lt_sub_right (le_of_succ_le_succ hle) (lt_of_succ_lt_succ h)

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

theorem sub.elim {motive : Nat → Prop}
    (x y : Nat)
    (h₁ : y ≤ x → (k : Nat) → x = y + k → motive k)
    (h₂ : x < y → motive 0)
    : motive (x - y) := by
  cases Nat.lt_or_ge x y with
  | inl hlt => rw [Nat.sub_eq_zero_of_le (Nat.le_of_lt hlt)]; exact h₂ hlt
  | inr hle => exact h₁ hle (x - y) (Nat.add_sub_of_le hle).symm

theorem succ_sub {m n : Nat} (h : n ≤ m) : succ m - n = succ (m - n) := by
  let ⟨k, hk⟩ := Nat.le.dest h
  rw [← hk, Nat.add_sub_cancel_left, ← add_succ, Nat.add_sub_cancel_left]

protected theorem sub_pos_of_lt (h : m < n) : 0 < n - m :=
  Nat.pos_iff_ne_zero.2 (Nat.sub_ne_zero_of_lt h)

protected theorem sub_sub (n m k : Nat) : n - m - k = n - (m + k) := by
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.add_succ, Nat.sub_succ, Nat.add_succ, Nat.sub_succ, ih]

protected theorem sub_le_sub_left (h : n ≤ m) (k : Nat) : k - m ≤ k - n :=
  match m, le.dest h with
  | _, ⟨a, rfl⟩ => by rw [← Nat.sub_sub]; apply sub_le

protected theorem sub_le_sub_right {n m : Nat} (h : n ≤ m) : ∀ k, n - k ≤ m - k
  | 0   => h
  | z+1 => pred_le_pred (Nat.sub_le_sub_right h z)

protected theorem sub_le_add_right_sub (a i j : Nat) : a - i ≤ a + j - i :=
  Nat.sub_le_sub_right (Nat.le_add_right ..) ..

protected theorem lt_of_sub_ne_zero (h : n - m ≠ 0) : m < n :=
  Nat.not_le.1 (mt Nat.sub_eq_zero_of_le h)

protected theorem sub_ne_zero_iff_lt : n - m ≠ 0 ↔ m < n :=
  ⟨Nat.lt_of_sub_ne_zero, Nat.sub_ne_zero_of_lt⟩

protected theorem lt_of_sub_pos (h : 0 < n - m) : m < n :=
  Nat.lt_of_sub_ne_zero (Nat.pos_iff_ne_zero.1 h)

protected theorem lt_of_sub_eq_succ (h : m - n = succ l) : n < m :=
  Nat.lt_of_sub_pos (h ▸ Nat.zero_lt_succ _)

protected theorem lt_of_sub_eq_sub_one (h : m - n = l + 1) : n < m :=
  Nat.lt_of_sub_pos (h ▸ Nat.zero_lt_succ _)

protected theorem sub_lt_left_of_lt_add {n k m : Nat} (H : n ≤ k) (h : k < n + m) : k - n < m := by
  have := Nat.sub_le_sub_right (succ_le_of_lt h) n
  rwa [Nat.add_sub_cancel_left, Nat.succ_sub H] at this

protected theorem sub_lt_right_of_lt_add {n k m : Nat} (H : n ≤ k) (h : k < m + n) : k - n < m :=
  Nat.sub_lt_left_of_lt_add H (Nat.add_comm .. ▸ h)

protected theorem le_of_sub_eq_zero : ∀ {n m}, n - m = 0 → n ≤ m
  | 0, _, _ => Nat.zero_le ..
  | _+1, _+1, h => Nat.succ_le_succ <| Nat.le_of_sub_eq_zero (Nat.succ_sub_succ .. ▸ h)

protected theorem le_of_sub_le_sub_right : ∀ {n m k : Nat}, k ≤ m → n - k ≤ m - k → n ≤ m
  | 0, _, _, _, _ => Nat.zero_le ..
  | _+1, _, 0, _, h₁ => h₁
  | _+1, _+1, _+1, h₀, h₁ => by
    simp only [Nat.succ_sub_succ] at h₁
    exact succ_le_succ <| Nat.le_of_sub_le_sub_right (le_of_succ_le_succ h₀) h₁

protected theorem sub_le_sub_iff_right {n : Nat} (h : k ≤ m) : n - k ≤ m - k ↔ n ≤ m :=
  ⟨Nat.le_of_sub_le_sub_right h, fun h => Nat.sub_le_sub_right h _⟩

protected theorem sub_eq_iff_eq_add {c : Nat} (h : b ≤ a) : a - b = c ↔ a = c + b :=
  ⟨fun | rfl => by rw [Nat.sub_add_cancel h], fun heq => by rw [heq, Nat.add_sub_cancel]⟩

protected theorem sub_eq_iff_eq_add' {c : Nat} (h : b ≤ a) : a - b = c ↔ a = b + c := by
  rw [Nat.add_comm, Nat.sub_eq_iff_eq_add h]

protected theorem sub_one_sub_lt_of_lt (h : a < b) : b - 1 - a < b := by
  rw [← Nat.sub_add_eq]
  exact sub_lt (zero_lt_of_lt h) (Nat.lt_add_right a Nat.one_pos)

/-! ## Mul sub distrib -/

theorem pred_mul (n m : Nat) : pred n * m = n * m - m := by
  cases n with
  | zero   => simp
  | succ n => rw [Nat.pred_succ, succ_mul, Nat.add_sub_cancel]

set_option linter.missingDocs false in
@[deprecated pred_mul (since := "2024-06-01")] abbrev mul_pred_left := @pred_mul

protected theorem sub_one_mul  (n m : Nat) : (n - 1) * m = n * m - m := by
  cases n with
  | zero   => simp
  | succ n =>
    rw [Nat.add_sub_cancel, add_one_mul, Nat.add_sub_cancel]

theorem mul_pred (n m : Nat) : n * pred m = n * m - n := by
  rw [Nat.mul_comm, pred_mul, Nat.mul_comm]

set_option linter.missingDocs false in
@[deprecated mul_pred (since := "2024-06-01")] abbrev mul_pred_right := @mul_pred

theorem mul_sub_one (n m : Nat) : n * (m - 1) = n * m - n := by
  rw [Nat.mul_comm, Nat.sub_one_mul , Nat.mul_comm]

protected theorem mul_sub_right_distrib (n m k : Nat) : (n - m) * k = n * k - m * k := by
  induction m with
  | zero => simp
  | succ m ih => rw [Nat.sub_succ, Nat.pred_mul, ih, succ_mul, Nat.sub_sub]; done

protected theorem mul_sub_left_distrib (n m k : Nat) : n * (m - k) = n * m - n * k := by
  rw [Nat.mul_comm, Nat.mul_sub_right_distrib, Nat.mul_comm m n, Nat.mul_comm n k]

/-! # Helper normalization theorems -/

theorem not_le_eq (a b : Nat) : (¬ (a ≤ b)) = (b + 1 ≤ a) :=
  Eq.propIntro Nat.gt_of_not_le Nat.not_le_of_gt
theorem not_ge_eq (a b : Nat) : (¬ (a ≥ b)) = (a + 1 ≤ b) :=
  not_le_eq b a

theorem not_lt_eq (a b : Nat) : (¬ (a < b)) = (b ≤ a) :=
  Eq.propIntro Nat.le_of_not_lt Nat.not_lt_of_le
theorem not_gt_eq (a b : Nat) : (¬ (a > b)) = (a ≤ b) :=
  not_lt_eq b a

@[csimp] theorem repeat_eq_repeatTR : @repeat = @repeatTR :=
  funext fun α => funext fun f => funext fun n => funext fun init =>
  let rec go : ∀ m n, repeatTR.loop f m (repeat f n init) = repeat f (m + n) init
    | 0,      n => by simp [repeatTR.loop]
    | succ m, n => by rw [repeatTR.loop, succ_add]; exact go m (succ n)
  (go n 0).symm

end Nat
