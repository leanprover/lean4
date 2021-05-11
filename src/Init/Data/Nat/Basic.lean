/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura
-/
prelude
import Init.SimpLemmas
universe u

namespace Nat

@[specialize] def foldAux {α : Type u} (f : Nat → α → α) (s : Nat) : Nat → α → α
  | 0,      a => a
  | succ n, a => foldAux f s n (f (s - (succ n)) a)

@[inline] def fold {α : Type u} (f : Nat → α → α) (n : Nat) (init : α) : α :=
  foldAux f n n init

@[inline] def foldRev {α : Type u} (f : Nat → α → α) (n : Nat) (init : α) : α :=
  let rec @[specialize] loop
    | 0,      a => a
    | succ n, a => loop n (f n a)
  loop n init

@[specialize] def anyAux (f : Nat → Bool) (s : Nat) : Nat → Bool
  | 0      => false
  | succ n => f (s - (succ n)) || anyAux f s n

/- `any f n = true` iff there is `i in [0, n-1]` s.t. `f i = true` -/
@[inline] def any (f : Nat → Bool) (n : Nat) : Bool :=
  anyAux f n n

@[inline] def all (f : Nat → Bool) (n : Nat) : Bool :=
  !any (fun i => !f i) n

@[inline] def repeat {α : Type u} (f : α → α) (n : Nat) (a : α) : α :=
  let rec @[specialize] loop
    | 0,      a => a
    | succ n, a => loop n (f a)
  loop n a

/- Nat.add theorems -/

@[simp] theorem zero_Eq : Nat.zero = 0 :=
  rfl

@[simp] protected theorem zero_add : ∀ (n : Nat), 0 + n = n
  | 0   => rfl
  | n+1 => congrArg succ (Nat.zero_add n)

theorem succ_add : ∀ (n m : Nat), (succ n) + m = succ (n + m)
  | n, 0   => rfl
  | n, m+1 => congrArg succ (succ_add n m)

theorem add_succ (n m : Nat) : n + succ m = succ (n + m) :=
  rfl

@[simp] protected theorem add_zero (n : Nat) : n + 0 = n :=
  rfl

theorem add_one (n : Nat) : n + 1 = succ n :=
  rfl

theorem succ_Eq_add_one (n : Nat) : succ n = n + 1 :=
  rfl

protected theorem add_comm : ∀ (n m : Nat), n + m = m + n
  | n, 0   => Eq.symm (Nat.zero_add n)
  | n, m+1 => by
    have succ (n + m) = succ (m + n) by apply congrArg; apply Nat.add_comm
    rw [succ_add m n]
    apply this

protected theorem add_assoc : ∀ (n m k : Nat), (n + m) + k = n + (m + k)
  | n, m, 0      => rfl
  | n, m, succ k => congrArg succ (Nat.add_assoc n m k)

protected theorem add_left_comm (n m k : Nat) : n + (m + k) = m + (n + k) := by
  rw [← Nat.add_assoc, Nat.add_comm n m, Nat.add_assoc]

protected theorem add_right_comm (n m k : Nat) : (n + m) + k = (n + k) + m := by
  rw [Nat.add_assoc, Nat.add_comm m k, ← Nat.add_assoc]

protected theorem add_left_cancel {n m k : Nat} : n + m = n + k → m = k := by
  induction n with
  | zero => simp; intros; assumption
  | succ n ih => simp [succ_add]; intro h; injection h with h; apply ih h

protected theorem add_right_cancel {n m k : Nat} (h : n + m = k + m) : n = k := by
  rw [Nat.add_comm n m, Nat.add_comm k m] at h
  apply Nat.add_left_cancel h

/- Nat.mul theorems -/

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

protected theorem right_distrib (n m k : Nat) : (n + m) * k = n * k + m * k :=
  have h₁ : (n + m) * k = k * (n + m)     from Nat.mul_comm ..
  have h₂ : k * (n + m) = k * n + k * m   from Nat.left_distrib ..
  have h₃ : k * n + k * m = n * k + k * m from Nat.mul_comm n k ▸ rfl
  have h₄ : n * k + k * m = n * k + m * k from Nat.mul_comm m k ▸ rfl
  ((h₁.trans h₂).trans h₃).trans h₄

protected theorem mul_assoc : ∀ (n m k : Nat), (n * m) * k = n * (m * k)
  | n, m, 0      => rfl
  | n, m, succ k =>
    have h₁ : n * m * succ k = n * m * (k + 1)              from rfl
    have h₂ : n * m * (k + 1) = (n * m * k) + n * m * 1     from Nat.left_distrib ..
    have h₃ : (n * m * k) + n * m * 1 = (n * m * k) + n * m by rw [Nat.mul_one (n*m)]
    have h₄ : (n * m * k) + n * m = (n * (m * k)) + n * m   by rw [Nat.mul_assoc n m k]
    have h₅ : (n * (m * k)) + n * m = n * (m * k + m)       from (Nat.left_distrib n (m*k) m).symm
    have h₆ : n * (m * k + m) = n * (m * succ k)            from Nat.mul_succ m k ▸ rfl
    ((((h₁.trans h₂).trans h₃).trans h₄).trans h₅).trans h₆

/- Inequalities -/

theorem succ_lt_succ {n m : Nat} : n < m → succ n < succ m :=
  succLeSucc

theorem lt_succ_of_le {n m : Nat} : n ≤ m → n < succ m :=
  succLeSucc

@[simp] protected theorem sub_zero (n : Nat) : n - 0 = n :=
  rfl

theorem succ_sub_succ_eq_sub (n m : Nat) : succ n - succ m = n - m := by
  induction m with
  | zero      => exact rfl
  | succ m ih => apply congrArg pred ih

theorem notSuccLeSelf (n : Nat) : ¬succ n ≤ n := by
  induction n with
  | zero      => intro h; apply notSuccLeZero 0 h
  | succ n ih => intro h; exact ih (leOfSuccLeSucc h)

protected theorem ltIrrefl (n : Nat) : ¬n < n :=
  notSuccLeSelf n

theorem predLe : ∀ (n : Nat), pred n ≤ n
  | zero   => rfl
  | succ n => leSucc _

theorem predLt : ∀ {n : Nat}, n ≠ 0 → pred n < n
  | zero,   h => absurd rfl h
  | succ n, h => lt_succ_of_le (Nat.leRefl _)

theorem subLe (n m : Nat) : n - m ≤ n := by
  induction m with
  | zero      => exact Nat.leRefl (n - 0)
  | succ m ih => apply Nat.leTrans (predLe (n - m)) ih

theorem subLt : ∀ {n m : Nat}, 0 < n → 0 < m → n - m < n
  | 0,   m,   h1, h2 => absurd h1 (Nat.ltIrrefl 0)
  | n+1, 0,   h1, h2 => absurd h2 (Nat.ltIrrefl 0)
  | n+1, m+1, h1, h2 =>
    Eq.symm (succ_sub_succ_eq_sub n m) ▸
      show n - m < succ n from
      lt_succ_of_le (subLe n m)

theorem sub_succ (n m : Nat) : n - succ m = pred (n - m) :=
  rfl

theorem succ_sub_succ (n m : Nat) : succ n - succ m = n - m :=
  succ_sub_succ_eq_sub n m

protected theorem sub_self : ∀ (n : Nat), n - n = 0
  | 0        => by rw [Nat.sub_zero]
  | (succ n) => by rw [succ_sub_succ, Nat.sub_self n]

protected theorem ltOfLtOfLe {n m k : Nat} : n < m → m ≤ k → n < k :=
  Nat.leTrans

protected theorem ltOfLtOfEq {n m k : Nat} : n < m → m = k → n < k :=
  fun h₁ h₂ => h₂ ▸ h₁

protected theorem leOfEq {n m : Nat} (p : n = m) : n ≤ m :=
  p ▸ Nat.leRefl n

theorem leOfSuccLe {n m : Nat} (h : succ n ≤ m) : n ≤ m :=
  Nat.leTrans (leSucc n) h

protected theorem leOfLt {n m : Nat} (h : n < m) : n ≤ m :=
  leOfSuccLe h

def lt.step {n m : Nat} : n < m → n < succ m := leStep

def succPos := zeroLtSucc

theorem eqZeroOrPos : ∀ (n : Nat), n = 0 ∨ n > 0
  | 0   => Or.inl rfl
  | n+1 => Or.inr (succPos _)

protected theorem ltOfLeOfLt {n m k : Nat} (h₁ : n ≤ m) : m < k → n < k :=
  Nat.leTrans (succLeSucc h₁)

def lt.base (n : Nat) : n < succ n := Nat.leRefl (succ n)

theorem ltSuccSelf (n : Nat) : n < succ n := lt.base n

protected theorem leTotal (m n : Nat) : m ≤ n ∨ n ≤ m :=
  match Nat.ltOrGe m n with
  | Or.inl h => Or.inl (Nat.leOfLt h)
  | Or.inr h => Or.inr h

protected theorem ltOfLeAndNe {m n : Nat} (h₁ : m ≤ n) (h₂ : m ≠ n) : m < n :=
  match Nat.eqOrLtOfLe h₁ with
  | Or.inl h => absurd h h₂
  | Or.inr h => h

theorem eqZeroOfLeZero {n : Nat} (h : n ≤ 0) : n = 0 :=
  Nat.leAntisymm h (zeroLe _)

theorem ltOfSuccLt {n m : Nat} : succ n < m → n < m :=
  leOfSuccLe

theorem lt_of_succ_lt_succ {n m : Nat} : succ n < succ m → n < m :=
  leOfSuccLeSucc

theorem ltOfSuccLe {n m : Nat} (h : succ n ≤ m) : n < m :=
  h

theorem succLeOfLt {n m : Nat} (h : n < m) : succ n ≤ m :=
  h

theorem ltOrEqOrLeSucc {m n : Nat} (h : m ≤ succ n) : m ≤ n ∨ m = succ n :=
  Decidable.byCases
    (fun (h' : m = succ n) => Or.inr h')
    (fun (h' : m ≠ succ n) =>
       have m < succ n from Nat.ltOfLeAndNe h h'
       have succ m ≤ succ n from succLeOfLt this
       Or.inl (leOfSuccLeSucc this))

theorem leAddRight : ∀ (n k : Nat), n ≤ n + k
  | n, 0   => Nat.leRefl n
  | n, k+1 => leSuccOfLe (leAddRight n k)

theorem leAddLeft (n m : Nat): n ≤ m + n :=
  Nat.add_comm n m ▸ leAddRight n m

theorem le.dest : ∀ {n m : Nat}, n ≤ m → Exists (fun k => n + k = m)
  | zero,   zero,   h => ⟨0, rfl⟩
  | zero,   succ n, h => ⟨succ n, Nat.add_comm 0 (succ n) ▸ rfl⟩
  | succ n, zero,   h => Bool.noConfusion h
  | succ n, succ m, h =>
    have n ≤ m from h
    have Exists (fun k => n + k = m) from dest this
    match this with
    | ⟨k, h⟩ => ⟨k, show succ n + k = succ m from ((succ_add n k).symm ▸ h ▸ rfl)⟩

theorem le.intro {n m k : Nat} (h : n + k = m) : n ≤ m :=
  h ▸ leAddRight n k

protected theorem notLeOfGt {n m : Nat} (h : n > m) : ¬ n ≤ m := fun h₁ =>
  match Nat.ltOrGe n m with
  | Or.inl h₂ => absurd (Nat.ltTrans h h₂) (Nat.ltIrrefl _)
  | Or.inr h₂ =>
    have Heq : n = m from Nat.leAntisymm h₁ h₂
    absurd (@Eq.subst _ _ _ _ Heq h) (Nat.ltIrrefl m)

theorem gtOfNotLe {n m : Nat} (h : ¬ n ≤ m) : n > m :=
  match Nat.ltOrGe m n with
  | Or.inl h₁ => h₁
  | Or.inr h₁ => absurd h₁ h

protected theorem addLeAddLeft {n m : Nat} (h : n ≤ m) (k : Nat) : k + n ≤ k + m :=
  match le.dest h with
  | ⟨w, hw⟩ =>
    have h₁ : k + n + w = k + (n + w) from Nat.add_assoc ..
    have h₂ : k + (n + w) = k + m     from congrArg _ hw
    le.intro <| h₁.trans h₂

protected theorem addLeAddRight {n m : Nat} (h : n ≤ m) (k : Nat) : n + k ≤ m + k := by
  rw [Nat.add_comm n k, Nat.add_comm m k]
  apply Nat.addLeAddLeft
  assumption

protected theorem addLtAddLeft {n m : Nat} (h : n < m) (k : Nat) : k + n < k + m :=
  ltOfSuccLe (add_succ k n ▸ Nat.addLeAddLeft (succLeOfLt h) k)

protected theorem addLtAddRight {n m : Nat} (h : n < m) (k : Nat) : n + k < m + k :=
  Nat.add_comm k m ▸ Nat.add_comm k n ▸ Nat.addLtAddLeft h k

protected theorem zeroLtOne : 0 < (1:Nat) :=
  zeroLtSucc 0

theorem addLeAdd {a b c d : Nat} (h₁ : a ≤ b) (h₂ : c ≤ d) : a + c ≤ b + d :=
  Nat.leTrans (Nat.addLeAddRight h₁ c) (Nat.addLeAddLeft h₂ b)

theorem addLtAdd {a b c d : Nat} (h₁ : a < b) (h₂ : c < d) : a + c < b + d :=
  Nat.ltTrans (Nat.addLtAddRight h₁ c) (Nat.addLtAddLeft h₂ b)

/- Basic theorems for comparing numerals -/

theorem natZeroEqZero : Nat.zero = 0 :=
  rfl

protected theorem oneNeZero : 1 ≠ (0 : Nat) :=
  fun h => Nat.noConfusion h

protected theorem zeroNeOne : 0 ≠ (1 : Nat) :=
  fun h => Nat.noConfusion h

theorem succNeZero (n : Nat) : succ n ≠ 0 :=
  fun h => Nat.noConfusion h

/- mul + order -/

theorem mulLeMulLeft {n m : Nat} (k : Nat) (h : n ≤ m) : k * n ≤ k * m :=
  match le.dest h with
  | ⟨l, hl⟩ =>
    have k * n + k * l = k * m from Nat.left_distrib k n l ▸ hl.symm ▸ rfl
    le.intro this

theorem mulLeMulRight {n m : Nat} (k : Nat) (h : n ≤ m) : n * k ≤ m * k :=
  Nat.mul_comm k m ▸ Nat.mul_comm k n ▸ mulLeMulLeft k h

protected theorem mulLeMul {n₁ m₁ n₂ m₂ : Nat} (h₁ : n₁ ≤ n₂) (h₂ : m₁ ≤ m₂) : n₁ * m₁ ≤ n₂ * m₂ :=
  Nat.leTrans (mulLeMulRight _ h₁) (mulLeMulLeft _ h₂)

protected theorem mulLtMulOfPosLeft {n m k : Nat} (h : n < m) (hk : k > 0) : k * n < k * m :=
  Nat.ltOfLtOfLe (Nat.addLtAddLeft hk _) (Nat.mul_succ k n ▸ Nat.mulLeMulLeft k (succLeOfLt h))

protected theorem mulLtMulOfPosRight {n m k : Nat} (h : n < m) (hk : k > 0) : n * k < m * k :=
  Nat.mul_comm k m ▸ Nat.mul_comm k n ▸ Nat.mulLtMulOfPosLeft h hk

protected theorem mulPos {n m : Nat} (ha : n > 0) (hb : m > 0) : n * m > 0 :=
  have h : 0 * m < n * m from Nat.mulLtMulOfPosRight ha hb
  Nat.zero_mul m ▸ h

/- power -/

theorem powSucc (n m : Nat) : n^(succ m) = n^m * n :=
  rfl

theorem powZero (n : Nat) : n^0 = 1 := rfl

theorem powLePowOfLeLeft {n m : Nat} (h : n ≤ m) : ∀ (i : Nat), n^i ≤ m^i
  | 0      => Nat.leRefl _
  | succ i => Nat.mulLeMul (powLePowOfLeLeft h i) h

theorem powLePowOfLeRight {n : Nat} (hx : n > 0) {i : Nat} : ∀ {j}, i ≤ j → n^i ≤ n^j
  | 0,      h =>
    have i = 0 from eqZeroOfLeZero h
    this.symm ▸ Nat.leRefl _
  | succ j, h =>
    match ltOrEqOrLeSucc h with
    | Or.inl h => show n^i ≤ n^j * n from
      have n^i * 1 ≤ n^j * n from Nat.mulLeMul (powLePowOfLeRight hx h) hx
      Nat.mul_one (n^i) ▸ this
    | Or.inr h =>
      h.symm ▸ Nat.leRefl _

theorem posPowOfPos {n : Nat} (m : Nat) (h : 0 < n) : 0 < n^m :=
  powLePowOfLeRight h (Nat.zeroLe _)

/- min/max -/

protected def min (n m : Nat) : Nat :=
  if n ≤ m then n else m

protected def max (n m : Nat) : Nat :=
  if n ≤ m then m else n

end Nat

namespace Prod

@[inline] def foldI {α : Type u} (f : Nat → α → α) (i : Nat × Nat) (a : α) : α :=
  Nat.foldAux f i.2 (i.2 - i.1) a

@[inline] def anyI (f : Nat → Bool) (i : Nat × Nat) : Bool :=
  Nat.anyAux f i.2 (i.2 - i.1)

@[inline] def allI (f : Nat → Bool) (i : Nat × Nat) : Bool :=
  Nat.anyAux (fun a => !f a) i.2 (i.2 - i.1)

end Prod
