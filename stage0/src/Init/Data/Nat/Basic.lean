/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura
-/
prelude
import Init.Core
universes u

namespace Nat

set_option bootstrap.gen_matcher_code false in
@[extern "lean_nat_dec_eq"]
  def beq : Nat → Nat → Bool
  | zero,   zero   => true
  | zero,   succ m => false
  | succ n, zero   => false
  | succ n, succ m => beq n m

theorem eqOfBeqEqTt : ∀ {n m : Nat}, beq n m = true → n = m
  | zero,   zero,   h => rfl
  | zero,   succ m, h => Bool.noConfusion h
  | succ n, zero,   h => Bool.noConfusion h
  | succ n, succ m, h =>
    have beq n m = true from h;
    have n = m from eqOfBeqEqTt this;
    congrArg succ this

theorem neOfBeqEqFf : ∀ {n m : Nat}, beq n m = false → n ≠ m
  | zero,   zero,   h₁, h₂ => Bool.noConfusion h₁
  | zero,   succ m, h₁, h₂ => Nat.noConfusion h₂
  | succ n, zero,   h₁, h₂ => Nat.noConfusion h₂
  | succ n, succ m, h₁, h₂ =>
    have beq n m = false from h₁;
    have n ≠ m from neOfBeqEqFf this;
    Nat.noConfusion h₂ (fun h₂ => absurd h₂ this)

@[extern "lean_nat_dec_eq"]
protected def decEq (n m : @& Nat) : Decidable (n = m) :=
  if h : beq n m = true then isTrue (eqOfBeqEqTt h)
  else isFalse (neOfBeqEqFf (eqFalseOfNeTrue h))

@[inline] instance : DecidableEq Nat := Nat.decEq

set_option bootstrap.gen_matcher_code false in
@[extern "lean_nat_dec_le"]
def ble : Nat → Nat → Bool
  | zero,   zero   => true
  | zero,   succ m => true
  | succ n, zero   => false
  | succ n, succ m => ble n m

protected def le (n m : Nat) : Prop :=
  ble n m = true

instance : HasLessEq Nat := ⟨Nat.le⟩

protected def lt (n m : Nat) : Prop :=
  Nat.le (succ n) m

instance : HasLess Nat := ⟨Nat.lt⟩

set_option bootstrap.gen_matcher_code false in
@[extern c inline "lean_nat_sub(#1, lean_box(1))"]
def pred : Nat → Nat
  | 0   => 0
  | a+1 => a

set_option bootstrap.gen_matcher_code false in
@[extern "lean_nat_sub"]
protected def sub : (@& Nat) → (@& Nat) → Nat
  | a, 0   => a
  | a, b+1 => pred (Nat.sub a b)

set_option bootstrap.gen_matcher_code false in
@[extern "lean_nat_mul"]
protected def mul : (@& Nat) → (@& Nat) → Nat
  | a, 0   => 0
  | a, b+1 => (Nat.mul a b) + a

instance : Sub Nat := ⟨Nat.sub⟩
instance : Mul Nat := ⟨Nat.mul⟩

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

set_option bootstrap.gen_matcher_code false in
@[extern "lean_nat_pow"]
protected def pow (m : @& Nat) : (@& Nat) → Nat
  | 0      => 1
  | succ n => Nat.pow m n * m

instance : Pow Nat Nat := ⟨Nat.pow⟩

/- Nat.add theorems -/

protected theorem zeroAdd : ∀ (n : Nat), 0 + n = n
  | 0   => rfl
  | n+1 => congrArg succ (Nat.zeroAdd n)

theorem succAdd : ∀ (n m : Nat), (succ n) + m = succ (n + m)
  | n, 0   => rfl
  | n, m+1 => congrArg succ (succAdd n m)

theorem addSucc (n m : Nat) : n + succ m = succ (n + m) :=
  rfl

protected theorem addZero (n : Nat) : n + 0 = n :=
  rfl

theorem addOne (n : Nat) : n + 1 = succ n :=
  rfl

theorem succEqAddOne (n : Nat) : succ n = n + 1 :=
  rfl

protected theorem addComm : ∀ (n m : Nat), n + m = m + n
  | n, 0   => Eq.symm (Nat.zeroAdd n)
  | n, m+1 => by
    have succ (n + m) = succ (m + n) by apply congrArg; apply Nat.addComm
    rw [succAdd m n]
    apply this

protected theorem addAssoc : ∀ (n m k : Nat), (n + m) + k = n + (m + k)
  | n, m, 0      => rfl
  | n, m, succ k => congrArg succ (Nat.addAssoc n m k)

protected theorem addLeftComm (n m k : Nat) : n + (m + k) = m + (n + k) := by
  rw [← Nat.addAssoc, Nat.addComm n m, Nat.addAssoc]
  exact rfl

protected theorem addRightComm (n m k : Nat) : (n + m) + k = (n + k) + m := by
  rw [Nat.addAssoc, Nat.addComm m k, ← Nat.addAssoc]
  exact rfl

protected theorem addLeftCancel : ∀ {n m k : Nat}, n + m = n + k → m = k
  | 0,      m, k, h => Nat.zeroAdd m ▸ Nat.zeroAdd k ▸ h
  | succ n, m, k, h =>
    have n+m = n+k from
      have succ (n + m) = succ (n + k) from succAdd n m ▸ succAdd n k ▸ h
      Nat.noConfusion this id
    Nat.addLeftCancel this

protected theorem addRightCancel {n m k : Nat} (h : n + m = k + m) : n = k :=
  have m + n = m + k from Nat.addComm n m ▸ Nat.addComm k m ▸ h
  Nat.addLeftCancel this

/- Nat.mul theorems -/

protected theorem mulZero (n : Nat) : n * 0 = 0 :=
  rfl

theorem mulSucc (n m : Nat) : n * succ m = n * m + n :=
  rfl

protected theorem zeroMul : ∀ (n : Nat), 0 * n = 0
  | 0      => rfl
  | succ n => mulSucc 0 n ▸ (Nat.zeroMul n).symm ▸ rfl

theorem succMul : ∀ (n m : Nat), (succ n) * m = (n * m) + m
  | n, 0      => rfl
  | n, succ m => by
    have succ (n * m + m + n) = succ (n * m + n + m) from
      congrArg succ (Nat.addRightComm ..)
    rw [mulSucc n m, mulSucc (succ n) m, succMul n m]
    assumption

protected theorem mulComm : ∀ (n m : Nat), n * m = m * n
  | n, 0      => (Nat.zeroMul n).symm ▸ (Nat.mulZero n).symm ▸ rfl
  | n, succ m => (mulSucc n m).symm ▸ (succMul m n).symm ▸ (Nat.mulComm n m).symm ▸ rfl

protected theorem mulOne : ∀ (n : Nat), n * 1 = n :=
  Nat.zeroAdd

protected theorem oneMul (n : Nat) : 1 * n = n :=
  Nat.mulComm n 1 ▸ Nat.mulOne n

protected theorem leftDistrib : ∀ (n m k : Nat), n * (m + k) = n * m + n * k
  | 0,      m, k => (Nat.zeroMul (m + k)).symm ▸ (Nat.zeroMul m).symm ▸ (Nat.zeroMul k).symm ▸ rfl
  | succ n, m, k =>
    have h₁ : succ n * (m + k) = n * (m + k) + (m + k)              from succMul ..
    have h₂ : n * (m + k) + (m + k) = (n * m + n * k) + (m + k)     from Nat.leftDistrib n m k ▸ rfl
    have h₃ : (n * m + n * k) + (m + k) = n * m + (n * k + (m + k)) from Nat.addAssoc ..
    have h₄ : n * m + (n * k + (m + k)) = n * m + (m + (n * k + k)) from congrArg (fun x => n*m + x) (Nat.addLeftComm ..)
    have h₅ : n * m + (m + (n * k + k)) = (n * m + m) + (n * k + k) from (Nat.addAssoc ..).symm
    have h₆ : (n * m + m) + (n * k + k) = (n * m + m) + succ n * k  from succMul n k ▸ rfl
    have h₇ : (n * m + m) + succ n * k = succ n * m + succ n * k    from succMul n m ▸ rfl
    (((((h₁.trans h₂).trans h₃).trans h₄).trans h₅).trans h₆).trans h₇

protected theorem rightDistrib (n m k : Nat) : (n + m) * k = n * k + m * k :=
  have h₁ : (n + m) * k = k * (n + m)     from Nat.mulComm ..
  have h₂ : k * (n + m) = k * n + k * m   from Nat.leftDistrib ..
  have h₃ : k * n + k * m = n * k + k * m from Nat.mulComm n k ▸ rfl
  have h₄ : n * k + k * m = n * k + m * k from Nat.mulComm m k ▸ rfl
  ((h₁.trans h₂).trans h₃).trans h₄

protected theorem mulAssoc : ∀ (n m k : Nat), (n * m) * k = n * (m * k)
  | n, m, 0      => rfl
  | n, m, succ k =>
    have h₁ : n * m * succ k = n * m * (k + 1)              from rfl
    have h₂ : n * m * (k + 1) = (n * m * k) + n * m * 1     from Nat.leftDistrib ..
    have h₃ : (n * m * k) + n * m * 1 = (n * m * k) + n * m by rw [Nat.mulOne (n*m)]; exact rfl
    have h₄ : (n * m * k) + n * m = (n * (m * k)) + n * m   by rw [Nat.mulAssoc n m k]; exact rfl
    have h₅ : (n * (m * k)) + n * m = n * (m * k + m)       from (Nat.leftDistrib n (m*k) m).symm
    have h₆ : n * (m * k + m) = n * (m * succ k)            from Nat.mulSucc m k ▸ rfl
    ((((h₁.trans h₂).trans h₃).trans h₄).trans h₅).trans h₆

/- Inequalities -/

protected def leRefl : ∀ (n : Nat), n ≤ n
  | zero   => rfl
  | succ n => Nat.leRefl n

theorem leSucc : ∀ (n : Nat), n ≤ succ n
  | zero   => rfl
  | succ n => leSucc n

theorem succLeSucc {n m : Nat} (h : n ≤ m) : succ n ≤ succ m :=
  h

theorem succLtSucc {n m : Nat} : n < m → succ n < succ m :=
  succLeSucc

theorem leStep : ∀ {n m : Nat}, n ≤ m → n ≤ succ m
  | zero,   zero,   h => rfl
  | zero,   succ n, h => rfl
  | succ n, zero,   h => Bool.noConfusion h
  | succ n, succ m, h =>
    have n ≤ m from h
    have n ≤ succ m from leStep this
    succLeSucc this

theorem zeroLe : ∀ (n : Nat), 0 ≤ n
  | zero   => rfl
  | succ n => rfl

theorem zeroLtSucc (n : Nat) : 0 < succ n :=
  succLeSucc (zeroLe n)

def succPos := zeroLtSucc

theorem notSuccLeZero : ∀ (n : Nat), succ n ≤ 0 → False
  | 0,   h => nomatch h
  | n+1, h => nomatch h

theorem notLtZero (n : Nat) : ¬ n < 0 :=
  notSuccLeZero n

theorem predLePred : ∀ {n m : Nat}, n ≤ m → pred n ≤ pred m
  | zero,   zero,   h => rfl
  | zero,   succ n, h => zeroLe n
  | succ n, zero,   h => Bool.noConfusion h
  | succ n, succ m, h => h

theorem leOfSuccLeSucc {n m : Nat} : succ n ≤ succ m → n ≤ m :=
  predLePred

@[extern "lean_nat_dec_le"]
instance decLe (n m : @& Nat) : Decidable (n ≤ m) :=
  decEq (ble n m) true

@[extern "lean_nat_dec_lt"]
instance decLt (n m : @& Nat) : Decidable (n < m) :=
  Nat.decLe (succ n) m

protected theorem eqOrLtOfLe : ∀ {n m: Nat}, n ≤ m → n = m ∨ n < m
  | zero,   zero,   h => Or.inl rfl
  | zero,   succ n, h => Or.inr $ zeroLe n
  | succ n, zero,   h => Bool.noConfusion h
  | succ n, succ m, h =>
    have n ≤ m from h
    have n = m ∨ n < m from Nat.eqOrLtOfLe this
    match this with
    | Or.inl h => Or.inl $ congrArg succ h
    | Or.inr h => Or.inr $ succLtSucc h

theorem ltSuccOfLe {n m : Nat} : n ≤ m → n < succ m :=
  succLeSucc

protected theorem subZero (n : Nat) : n - 0 = n :=
  rfl

theorem succSubSuccEqSub (n m : Nat) : succ n - succ m = n - m := by
  induction m
  | zero      => exact rfl
  | succ m ih => apply congrArg pred ih

theorem notSuccLeSelf (n : Nat) : ¬succ n ≤ n := by
  induction n
  | zero      => intro h; apply notSuccLeZero 0 h
  | succ n ih => intro h; exact ih (leOfSuccLeSucc h)

protected theorem ltIrrefl (n : Nat) : ¬n < n :=
  notSuccLeSelf n

protected theorem leTrans : ∀ {n m k : Nat}, n ≤ m → m ≤ k → n ≤ k
  | zero,   m,      k,      h₁, h₂ => zeroLe _
  | succ n, zero,   k,      h₁, h₂ => Bool.noConfusion h₁
  | succ n, succ m, zero,   h₁, h₂ => Bool.noConfusion h₂
  | succ n, succ m, succ k, h₁, h₂ =>
    have h₁' : n ≤ m from h₁
    have h₂' : m ≤ k from h₂
    have n ≤ k from Nat.leTrans h₁' h₂'
    succLeSucc this

theorem predLe : ∀ (n : Nat), pred n ≤ n
  | zero   => rfl
  | succ n => leSucc _

theorem predLt : ∀ {n : Nat}, n ≠ 0 → pred n < n
  | zero,   h => absurd rfl h
  | succ n, h => ltSuccOfLe (Nat.leRefl _)

theorem subLe (n m : Nat) : n - m ≤ n := by
  induction m
  | zero      => exact Nat.leRefl (n - 0)
  | succ m ih => apply Nat.leTrans (predLe (n - m)) ih

theorem subLt : ∀ {n m : Nat}, 0 < n → 0 < m → n - m < n
  | 0,   m,   h1, h2 => absurd h1 (Nat.ltIrrefl 0)
  | n+1, 0,   h1, h2 => absurd h2 (Nat.ltIrrefl 0)
  | n+1, m+1, h1, h2 =>
    Eq.symm (succSubSuccEqSub n m) ▸
      show n - m < succ n from
      ltSuccOfLe (subLe n m)

protected theorem ltOfLtOfLe {n m k : Nat} : n < m → m ≤ k → n < k :=
  Nat.leTrans

protected theorem ltOfLtOfEq {n m k : Nat} : n < m → m = k → n < k :=
  fun h₁ h₂ => h₂ ▸ h₁

protected theorem leOfEq {n m : Nat} (p : n = m) : n ≤ m :=
  p ▸ Nat.leRefl n

theorem leSuccOfLe {n m : Nat} (h : n ≤ m) : n ≤ succ m :=
  Nat.leTrans h (leSucc m)

theorem leOfSuccLe {n m : Nat} (h : succ n ≤ m) : n ≤ m :=
  Nat.leTrans (leSucc n) h

protected theorem leOfLt {n m : Nat} (h : n < m) : n ≤ m :=
  leOfSuccLe h

def lt.step {n m : Nat} : n < m → n < succ m := leStep

theorem eqZeroOrPos : ∀ (n : Nat), n = 0 ∨ n > 0
  | 0   => Or.inl rfl
  | n+1 => Or.inr (succPos _)

protected theorem ltTrans {n m k : Nat} (h₁ : n < m) : m < k → n < k :=
  Nat.leTrans (leStep h₁)

protected theorem ltOfLeOfLt {n m k : Nat} (h₁ : n ≤ m) : m < k → n < k :=
  Nat.leTrans (succLeSucc h₁)

def lt.base (n : Nat) : n < succ n := Nat.leRefl (succ n)

theorem ltSuccSelf (n : Nat) : n < succ n := lt.base n

protected theorem leAntisymm : ∀ {n m : Nat}, n ≤ m → m ≤ n → n = m
  | zero,   zero,   h₁, h₂ => rfl
  | succ n, zero,   h₁, h₂ => Bool.noConfusion h₁
  | zero,   succ m, h₁, h₂ => Bool.noConfusion h₂
  | succ n, succ m, h₁, h₂ =>
    have h₁' : n ≤ m from h₁
    have h₂' : m ≤ n from h₂
    have n = m from Nat.leAntisymm h₁' h₂'
    congrArg succ this

protected theorem ltOrGe (n m : Nat) : n < m ∨ n ≥ m := by
  induction m
  | zero => apply Or.inr; apply zeroLe n
  | succ m ih =>
    cases ih
    | inl h => apply Or.inl; apply leSuccOfLe h
    | inr h =>
      cases Nat.eqOrLtOfLe h
      | inl h1 => apply Or.inl; subst h1; apply ltSuccSelf m
      | inr h1 => apply Or.inr h1

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

theorem ltOfSuccLtSucc {n m : Nat} : succ n < succ m → n < m :=
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
  Nat.addComm n m ▸ leAddRight n m

theorem le.dest : ∀ {n m : Nat}, n ≤ m → Exists (fun k => n + k = m)
  | zero,   zero,   h => ⟨0, rfl⟩
  | zero,   succ n, h => ⟨succ n, Nat.addComm 0 (succ n) ▸ rfl⟩
  | succ n, zero,   h => Bool.noConfusion h
  | succ n, succ m, h =>
    have n ≤ m from h
    have Exists (fun k => n + k = m) from dest this
    match this with
    | ⟨k, h⟩ => ⟨k, show succ n + k = succ m from ((succAdd n k).symm ▸ h ▸ rfl)⟩

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

protected theorem ltOfLeOfNe {n m : Nat} (h₁ : n ≤ m) (h₂ : n ≠ m) : n < m :=
  match Nat.ltOrGe n m with
  | Or.inl h₃ => h₃
  | Or.inr h₃ => absurd (Nat.leAntisymm h₁ h₃) h₂

protected theorem addLeAddLeft {n m : Nat} (h : n ≤ m) (k : Nat) : k + n ≤ k + m :=
  match le.dest h with
  | ⟨w, hw⟩ =>
    have h₁ : k + n + w = k + (n + w) from Nat.addAssoc ..
    have h₂ : k + (n + w) = k + m     from congrArg _ hw
    le.intro $ h₁.trans h₂

protected theorem addLeAddRight {n m : Nat} (h : n ≤ m) (k : Nat) : n + k ≤ m + k := by
  rw [Nat.addComm n k, Nat.addComm m k]
  apply Nat.addLeAddLeft
  assumption

protected theorem addLtAddLeft {n m : Nat} (h : n < m) (k : Nat) : k + n < k + m :=
  ltOfSuccLe (addSucc k n ▸ Nat.addLeAddLeft (succLeOfLt h) k)

protected theorem addLtAddRight {n m : Nat} (h : n < m) (k : Nat) : n + k < m + k :=
  Nat.addComm k m ▸ Nat.addComm k n ▸ Nat.addLtAddLeft h k

protected theorem zeroLtOne : 0 < (1:Nat) :=
  zeroLtSucc 0

theorem leOfLtSucc {m n : Nat} : m < succ n → m ≤ n :=
  leOfSuccLeSucc

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
    have k * n + k * l = k * m from Nat.leftDistrib k n l ▸ hl.symm ▸ rfl
    le.intro this

theorem mulLeMulRight {n m : Nat} (k : Nat) (h : n ≤ m) : n * k ≤ m * k :=
  Nat.mulComm k m ▸ Nat.mulComm k n ▸ mulLeMulLeft k h

protected theorem mulLeMul {n₁ m₁ n₂ m₂ : Nat} (h₁ : n₁ ≤ n₂) (h₂ : m₁ ≤ m₂) : n₁ * m₁ ≤ n₂ * m₂ :=
  Nat.leTrans (mulLeMulRight _ h₁) (mulLeMulLeft _ h₂)

protected theorem mulLtMulOfPosLeft {n m k : Nat} (h : n < m) (hk : k > 0) : k * n < k * m :=
  Nat.ltOfLtOfLe (Nat.addLtAddLeft hk _) (Nat.mulSucc k n ▸ Nat.mulLeMulLeft k (succLeOfLt h))

protected theorem mulLtMulOfPosRight {n m k : Nat} (h : n < m) (hk : k > 0) : n * k < m * k :=
  Nat.mulComm k m ▸ Nat.mulComm k n ▸ Nat.mulLtMulOfPosLeft h hk

protected theorem mulPos {n m : Nat} (ha : n > 0) (hb : m > 0) : n * m > 0 :=
  have h : 0 * m < n * m from Nat.mulLtMulOfPosRight ha hb
  Nat.zeroMul m ▸ h

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
      Nat.mulOne (n^i) ▸ this
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
