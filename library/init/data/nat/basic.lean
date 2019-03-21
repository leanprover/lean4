/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura
-/
prelude
import init.core
universes u

notation `ℕ` := Nat

namespace Nat

@[extern cpp "lean::nat_dec_eq"]
def beq : Nat → Nat → Bool
| zero     zero     := true
| zero     (succ m) := false
| (succ n) zero     := false
| (succ n) (succ m) := beq n m

theorem eqOfBeqEqTt : ∀ {n m : Nat}, beq n m = true → n = m
| zero     zero     h := rfl
| zero     (succ m) h := Bool.noConfusion h
| (succ n) zero     h := Bool.noConfusion h
| (succ n) (succ m) h :=
  have beq n m = true, from h,
  have n = m, from eqOfBeqEqTt this,
  congrArg succ this

theorem neOfBeqEqFf : ∀ {n m : Nat}, beq n m = false → n ≠ m
| zero     zero     h₁ h₂ := Bool.noConfusion h₁
| zero     (succ m) h₁ h₂ := Nat.noConfusion h₂
| (succ n) zero     h₁ h₂ := Nat.noConfusion h₂
| (succ n) (succ m) h₁ h₂ :=
  have beq n m = false, from h₁,
  have n ≠ m, from neOfBeqEqFf this,
  Nat.noConfusion h₂ (λ h₂, absurd h₂ this)

@[extern cpp "lean::nat_dec_eq"]
protected def decEq (n m : @& Nat) : Decidable (n = m) :=
if h : beq n m = true then isTrue (eqOfBeqEqTt h)
else isFalse (neOfBeqEqFf (eqFfOfNeTt h))

@[inline] instance : DecidableEq Nat :=
{decEq := Nat.decEq}

@[extern cpp "lean::nat_dec_le"]
def ble : Nat → Nat → Bool
| zero     zero     := true
| zero     (succ m) := true
| (succ n) zero     := false
| (succ n) (succ m) := ble n m

protected def le (n m : Nat) : Prop :=
ble n m = true

instance : HasLe Nat :=
⟨Nat.le⟩

protected def lt (n m : Nat) : Prop :=
Nat.le (succ n) m

instance : HasLt Nat :=
⟨Nat.lt⟩

@[extern cpp inline "lean::nat_sub(#1, lean::box(1))"]
def pred : Nat → Nat
| 0     := 0
| (a+1) := a

@[extern cpp "lean::nat_sub"]
protected def sub : (@& Nat) → (@& Nat) → Nat
| a 0     := a
| a (b+1) := pred (sub a b)

@[extern cpp "lean::nat_mul"]
protected def mul : (@& Nat) → (@& Nat) → Nat
| a 0     := 0
| a (b+1) := (mul a b) + a

instance : HasSub Nat :=
⟨Nat.sub⟩

instance : HasMul Nat :=
⟨Nat.mul⟩

@[specialize] def repeatCore {α : Type u} (f : Nat → α → α) (s : Nat) : Nat → α → α
| 0         a := a
| (succ n)  a := repeatCore n (f (s - (succ n)) a)

@[inline] def repeat {α : Type u} (f : Nat → α → α) (n : Nat) (a : α) : α :=
repeatCore f n n a

protected def pow (m : Nat) : Nat → Nat
| 0        := 1
| (succ n) := pow n * m

instance : HasPow Nat Nat :=
⟨Nat.pow⟩

/- Nat.add theorems -/

protected theorem zeroAdd : ∀ n : Nat, 0 + n = n
| 0     := rfl
| (n+1) := congrArg succ (zeroAdd n)

theorem succAdd : ∀ n m : Nat, (succ n) + m = succ (n + m)
| n 0     := rfl
| n (m+1) := congrArg succ (succAdd n m)

theorem addSucc (n m : Nat) : n + succ m = succ (n + m) :=
rfl

protected theorem addZero (n : Nat) : n + 0 = n :=
rfl

theorem addOne (n : Nat) : n + 1 = succ n :=
rfl

theorem succEqAddOne (n : Nat) : succ n = n + 1 :=
rfl

protected theorem addComm : ∀ n m : Nat, n + m = m + n
| n 0     := Eq.symm (Nat.zeroAdd n)
| n (m+1) :=
  suffices succ (n + m) = succ (m + n), from
    Eq.symm (succAdd m n) ▸ this,
  congrArg succ (addComm n m)

protected theorem addAssoc : ∀ n m k : Nat, (n + m) + k = n + (m + k)
| n m 0        := rfl
| n m (succ k) := congrArg succ (addAssoc n m k)

protected theorem addLeftComm : ∀ (n m k : Nat), n + (m + k) = m + (n + k) :=
leftComm Nat.add Nat.addComm Nat.addAssoc

protected theorem addRightComm : ∀ (n m k : Nat), (n + m) + k = (n + k) + m :=
rightComm Nat.add Nat.addComm Nat.addAssoc

protected theorem addLeftCancel : ∀ {n m k : Nat}, n + m = n + k → m = k
| 0        m k h := Nat.zeroAdd m ▸ Nat.zeroAdd k ▸ h
| (succ n) m k h :=
  have n+m = n+k, from
    have succ (n + m) = succ (n + k), from succAdd n m ▸ succAdd n k ▸ h,
    Nat.noConfusion this id,
  addLeftCancel this

protected theorem addRightCancel {n m k : Nat} (h : n + m = k + m) : n = k :=
have m + n = m + k, from Nat.addComm n m ▸ Nat.addComm k m ▸ h,
Nat.addLeftCancel this

/- Nat.mul theorems -/

protected theorem mulZero (n : Nat) : n * 0 = 0 :=
rfl

theorem mulSucc (n m : Nat) : n * succ m = n * m + n :=
rfl

protected theorem zeroMul : ∀ (n : Nat), 0 * n = 0
| 0        := rfl
| (succ n) := (mulSucc 0 n).symm ▸ (zeroMul n).symm ▸ rfl

theorem succMul : ∀ (n m : Nat), (succ n) * m = (n * m) + m
| n 0        := rfl
| n (succ m) :=
  have succ (n * m + m + n) = succ (n * m + n + m), from
    congrArg succ (Nat.addRightComm _ _ _),
  (mulSucc n m).symm ▸ (mulSucc (succ n) m).symm ▸ (succMul n m).symm ▸ this

protected theorem mulComm : ∀ (n m : Nat), n * m = m * n
| n 0        := (Nat.zeroMul n).symm ▸ (Nat.mulZero n).symm ▸ rfl
| n (succ m) := (mulSucc n m).symm ▸ (succMul m n).symm ▸ (mulComm n m).symm ▸ rfl

protected theorem mulOne : ∀ (n : Nat), n * 1 = n :=
Nat.zeroAdd

protected theorem oneMul (n : Nat) : 1 * n = n :=
Nat.mulComm n 1 ▸ Nat.mulOne n

local infix `◾`:50 := Eq.trans

protected theorem leftDistrib : ∀ (n m k : Nat), n * (m + k) = n * m + n * k
| 0        m k := (Nat.zeroMul (m + k)).symm ▸ (Nat.zeroMul m).symm ▸ (Nat.zeroMul k).symm ▸ rfl
| (succ n) m k :=
  have h₁ : succ n * (m + k) = n * (m + k) + (m + k),              from succMul _ _,
  have h₂ : n * (m + k) + (m + k) = (n * m + n * k) + (m + k),     from leftDistrib n m k ▸ rfl,
  have h₃ : (n * m + n * k) + (m + k) = n * m + (n * k + (m + k)), from Nat.addAssoc _ _ _,
  have h₄ : n * m + (n * k + (m + k)) = n * m + (m + (n * k + k)), from congrArg (λ x, n*m + x) (Nat.addLeftComm _ _ _),
  have h₅ : n * m + (m + (n * k + k)) = (n * m + m) + (n * k + k), from (Nat.addAssoc _ _ _).symm,
  have h₆ : (n * m + m) + (n * k + k) = (n * m + m) + succ n * k,  from succMul n k ▸ rfl,
  have h₇ : (n * m + m) + succ n * k = succ n * m + succ n * k,    from succMul n m ▸ rfl,
  h₁ ◾ h₂ ◾ h₃ ◾ h₄ ◾ h₅ ◾ h₆ ◾ h₇

protected theorem rightDistrib (n m k : Nat) : (n + m) * k = n * k + m * k :=
have h₁ : (n + m) * k = k * (n + m),     from Nat.mulComm _ _,
have h₂ : k * (n + m) = k * n + k * m,   from Nat.leftDistrib _ _ _,
have h₃ : k * n + k * m = n * k + k * m, from Nat.mulComm n k ▸ rfl,
have h₄ : n * k + k * m = n * k + m * k, from Nat.mulComm m k ▸ rfl,
h₁ ◾ h₂ ◾ h₃ ◾ h₄

protected theorem mulAssoc : ∀ (n m k : Nat), (n * m) * k = n * (m * k)
| n m 0        := rfl
| n m (succ k) :=
  have h₁ : n * m * succ k = n * m * (k + 1),              from rfl,
  have h₂ : n * m * (k + 1) = (n * m * k) + n * m * 1,     from Nat.leftDistrib _ _ _,
  have h₃ : (n * m * k) + n * m * 1 = (n * m * k) + n * m, from (Nat.mulOne (n*m)).symm ▸ rfl,
  have h₄ : (n * m * k) + n * m = (n * (m * k)) + n * m,   from (mulAssoc n m k).symm ▸ rfl,
  have h₅ : (n * (m * k)) + n * m = n * (m * k + m),       from (Nat.leftDistrib n (m*k) m).symm,
  have h₆ : n * (m * k + m) = n * (m * succ k),            from Nat.mulSucc m k ▸ rfl,
h₁ ◾ h₂ ◾ h₃ ◾ h₄ ◾ h₅ ◾ h₆

/- Inequalities -/

protected def leRefl : ∀ n : Nat, n ≤ n
| zero     := rfl
| (succ n) := leRefl n

theorem leSucc : ∀ (n : Nat), n ≤ succ n
| zero     := rfl
| (succ n) := leSucc n

theorem succLeSucc {n m : Nat} (h : n ≤ m) : succ n ≤ succ m :=
h

theorem succLtSucc {n m : Nat} : n < m → succ n < succ m :=
succLeSucc

theorem leStep : ∀ {n m : Nat}, n ≤ m → n ≤ succ m
| zero     zero     h := rfl
| zero     (succ n) h := rfl
| (succ n) zero     h := Bool.noConfusion h
| (succ n) (succ m) h :=
  have n ≤ m, from h,
  have n ≤ succ m, from leStep this,
  succLeSucc this

theorem zeroLe : ∀ (n : Nat), 0 ≤ n
| zero     := rfl
| (succ n) := rfl

theorem zeroLtSucc (n : Nat) : 0 < succ n :=
succLeSucc (zeroLe n)

def succPos := zeroLtSucc

theorem notSuccLeZero : ∀ (n : Nat), succ n ≤ 0 → False
.

theorem notLtZero (n : Nat) : ¬ n < 0 :=
notSuccLeZero n

theorem predLePred : ∀ {n m : Nat}, n ≤ m → pred n ≤ pred m
| zero     zero     h := rfl
| zero     (succ n) h := zeroLe n
| (succ n) zero     h := Bool.noConfusion h
| (succ n) (succ m) h := h

theorem leOfSuccLeSucc {n m : Nat} : succ n ≤ succ m → n ≤ m :=
predLePred

@[extern cpp "lean::nat_dec_le"]
instance decLe (n m : @& Nat) : Decidable (n ≤ m) :=
decEq (ble n m) true

@[extern cpp "lean::nat_dec_lt"]
instance decLt (n m : @& Nat) : Decidable (n < m) :=
Nat.decLe (succ n) m

protected theorem eqOrLtOfLe : ∀ {n m: Nat}, n ≤ m → n = m ∨ n < m
| zero     zero     h := Or.inl rfl
| zero     (succ n) h := Or.inr $ zeroLe n
| (succ n) zero     h := Bool.noConfusion h
| (succ n) (succ m) h :=
  have n ≤ m, from h,
  have n = m ∨ n < m, from eqOrLtOfLe this,
  Or.elim this
   (λ h, Or.inl $ congrArg succ h)
   (λ h, Or.inr $ succLtSucc h)

theorem ltSuccOfLe {n m : Nat} : n ≤ m → n < succ m :=
succLeSucc

protected theorem subZero (n : Nat) : n - 0 = n :=
rfl

theorem succSubSuccEqSub (n m : Nat) : succ n - succ m = n - m :=
Nat.recOn m
  (show succ n - succ zero = n - zero, from (Eq.refl (succ n - succ zero)))
  (λ m, congrArg pred)

theorem notSuccLeSelf : ∀ n : Nat, ¬succ n ≤ n :=
λ n, Nat.rec (notSuccLeZero 0) (λ a b c, b (leOfSuccLeSucc c)) n

protected theorem ltIrrefl (n : Nat) : ¬n < n :=
notSuccLeSelf n

protected theorem leTrans : ∀ {n m k : Nat}, n ≤ m → m ≤ k → n ≤ k
| zero     m        k        h₁ h₂ := zeroLe _
| (succ n) zero     k        h₁ h₂ := Bool.noConfusion h₁
| (succ n) (succ m) zero     h₁ h₂ := Bool.noConfusion h₂
| (succ n) (succ m) (succ k) h₁ h₂ :=
  have h₁' : n ≤ m, from h₁,
  have h₂' : m ≤ k, from h₂,
  have n ≤ k, from leTrans h₁' h₂',
  succLeSucc this

theorem predLe : ∀ (n : Nat), pred n ≤ n
| zero     := rfl
| (succ n) := leSucc _

theorem predLt : ∀ {n : Nat}, n ≠ 0 → pred n < n
| zero     h := absurd rfl h
| (succ n) h := ltSuccOfLe (Nat.leRefl _)

theorem subLe (n m : Nat) : n - m ≤ n :=
Nat.recOn m (Nat.leRefl (n - 0)) (λ m, Nat.leTrans (predLe (n - m)))

theorem subLt : ∀ {n m : Nat}, 0 < n → 0 < m → n - m < n
| 0     m     h1 h2 := absurd h1 (Nat.ltIrrefl 0)
| (n+1) 0     h1 h2 := absurd h2 (Nat.ltIrrefl 0)
| (n+1) (m+1) h1 h2 :=
  Eq.symm (succSubSuccEqSub n m) ▸
    show n - m < succ n, from
    ltSuccOfLe (subLe n m)

protected theorem ltOfLtOfLe {n m k : Nat} : n < m → m ≤ k → n < k :=
Nat.leTrans

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
| 0     := Or.inl rfl
| (n+1) := Or.inr (succPos _)

protected theorem ltTrans {n m k : Nat} (h₁ : n < m) : m < k → n < k :=
Nat.leTrans (leStep h₁)

protected theorem ltOfLeOfLt {n m k : Nat} (h₁ : n ≤ m) : m < k → n < k :=
Nat.leTrans (succLeSucc h₁)

def lt.base (n : Nat) : n < succ n := Nat.leRefl (succ n)

theorem ltSuccSelf (n : Nat) : n < succ n := lt.base n

protected theorem leAntisymm : ∀ {n m : Nat}, n ≤ m → m ≤ n → n = m
| zero     zero     h₁ h₂ := rfl
| (succ n) zero     h₁ h₂ := Bool.noConfusion h₁
| zero     (succ m) h₁ h₂ := Bool.noConfusion h₂
| (succ n) (succ m) h₁ h₂ :=
  have h₁' : n ≤ m, from h₁,
  have h₂' : m ≤ n, from h₂,
  have n = m, from leAntisymm h₁' h₂',
  congrArg succ this

protected theorem ltOrGe : ∀ (n m : Nat), n < m ∨ n ≥ m
| n 0     := Or.inr (zeroLe n)
| n (m+1) :=
  match ltOrGe n m with
  | Or.inl h := Or.inl (leSuccOfLe h)
  | Or.inr h :=
    match Nat.eqOrLtOfLe h with
    | Or.inl h1 := Or.inl (h1 ▸ ltSuccSelf m)
    | Or.inr h1 := Or.inr h1

protected theorem leTotal (m n : Nat) : m ≤ n ∨ n ≤ m :=
Or.elim (Nat.ltOrGe m n)
  (λ h, Or.inl (Nat.leOfLt h))
  Or.inr

protected theorem ltOfLeAndNe {m n : Nat} (h1 : m ≤ n) : m ≠ n → m < n :=
resolveRight (Or.swap (Nat.eqOrLtOfLe h1))

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
  (λ h' : m = succ n, Or.inr h')
  (λ h' : m ≠ succ n,
     have m < succ n, from Nat.ltOfLeAndNe h h',
     have succ m ≤ succ n, from succLeOfLt this,
     Or.inl (leOfSuccLeSucc this))

theorem leAddRight : ∀ (n k : Nat), n ≤ n + k
| n 0     := Nat.leRefl n
| n (k+1) := leSuccOfLe (leAddRight n k)

theorem leAddLeft (n m : Nat): n ≤ m + n :=
Nat.addComm n m ▸ leAddRight n m

theorem le.dest : ∀ {n m : Nat}, n ≤ m → ∃ k, n + k = m
| zero     zero     h := ⟨0, rfl⟩
| zero     (succ n) h := ⟨succ n, show 0 + succ n = succ n, from (Nat.addComm 0 (succ n)).symm ▸ rfl⟩
| (succ n) zero     h := Bool.noConfusion h
| (succ n) (succ m) h :=
  have n ≤ m, from h,
  have ∃ k, n + k = m, from le.dest this,
  match this with
  | ⟨k, h⟩ := ⟨k, show succ n + k = succ m, from ((succAdd n k).symm ▸ h ▸ rfl)⟩

theorem le.intro {n m k : Nat} (h : n + k = m) : n ≤ m :=
h ▸ leAddRight n k

protected theorem notLeOfGt {n m : Nat} (h : n > m) : ¬ n ≤ m :=
λ h₁, Or.elim (Nat.ltOrGe n m)
  (λ h₂, absurd (Nat.ltTrans h h₂) (Nat.ltIrrefl _))
  (λ h₂, have Heq : n = m, from Nat.leAntisymm h₁ h₂, absurd (@Eq.subst _ _ _ _ Heq h) (Nat.ltIrrefl m))

theorem gtOfNotLe {n m : Nat} (h : ¬ n ≤ m) : n > m :=
Or.elim (Nat.ltOrGe m n)
  (λ h₁, h₁)
  (λ h₁, absurd h₁ h)

protected theorem ltOfLeOfNe {n m : Nat} (h₁ : n ≤ m) (h₂ : n ≠ m) : n < m :=
Or.elim (Nat.ltOrGe n m)
  (λ h₃, h₃)
  (λ h₃, absurd (Nat.leAntisymm h₁ h₃) h₂)

protected theorem addLeAddLeft {n m : Nat} (h : n ≤ m) (k : Nat) : k + n ≤ k + m :=
match le.dest h with
| ⟨w, hw⟩ :=
  have h₁ : k + n + w = k + (n + w), from Nat.addAssoc _ _ _,
  have h₂ : k + (n + w) = k + m,     from congrArg _ hw,
  le.intro $ h₁ ◾ h₂

protected theorem addLeAddRight {n m : Nat} (h : n ≤ m) (k : Nat) : n + k ≤ m + k :=
have h₁ : n + k = k + n, from Nat.addComm _ _,
have h₂ : k + n ≤ k + m, from Nat.addLeAddLeft h k,
have h₃ : k + m = m + k, from Nat.addComm _ _,
transRelLeft (≤) (transRelRight (≤) h₁ h₂) h₃

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
assume h, Nat.noConfusion h

protected theorem zeroNeOne : 0 ≠ (1 : Nat) :=
assume h, Nat.noConfusion h

theorem succNeZero (n : Nat) : succ n ≠ 0 :=
assume h, Nat.noConfusion h

protected theorem bit0SuccEq (n : Nat) : bit0 (succ n) = succ (succ (bit0 n)) :=
show succ (succ n + n) = succ (succ (n + n)), from
congrArg succ (succAdd n n)

protected theorem zeroLtBit0 : ∀ {n : Nat}, n ≠ 0 → 0 < bit0 n
| 0        h := absurd rfl h
| (succ n) h :=
  have h₁ : 0 < succ (succ (bit0 n)),             from zeroLtSucc _,
  have h₂ : succ (succ (bit0 n)) = bit0 (succ n), from (Nat.bit0SuccEq n).symm,
  transRelLeft (<) h₁ h₂

protected theorem zeroLtBit1 (n : Nat) : 0 < bit1 n :=
zeroLtSucc _

protected theorem bit0NeZero : ∀ {n : Nat}, n ≠ 0 → bit0 n ≠ 0
| 0     h := absurd rfl h
| (n+1) h :=
  suffices (n+1) + (n+1) ≠ 0, from this,
  suffices succ ((n+1) + n) ≠ 0, from this,
  λ h, Nat.noConfusion h

protected theorem bit1NeZero (n : Nat) : bit1 n ≠ 0 :=
show succ (n + n) ≠ 0, from
λ h, Nat.noConfusion h

protected theorem bit1EqSuccBit0 (n : Nat) : bit1 n = succ (bit0 n) :=
rfl

protected theorem bit1SuccEq (n : Nat) : bit1 (succ n) = succ (succ (bit1 n)) :=
Eq.trans (Nat.bit1EqSuccBit0 (succ n)) (congrArg succ (Nat.bit0SuccEq n))

protected theorem bit1NeOne : ∀ {n : Nat}, n ≠ 0 → bit1 n ≠ 1
| 0     h h1 := absurd rfl h
| (n+1) h h1 := Nat.noConfusion h1 (λ h2, absurd h2 (succNeZero _))

protected theorem bit0NeOne : ∀ n : Nat, bit0 n ≠ 1
| 0     h := absurd h (ne.symm Nat.oneNeZero)
| (n+1) h :=
  have h1 : succ (succ (n + n)) = 1, from succAdd n n ▸ h,
  Nat.noConfusion h1
    (λ h2, absurd h2 (succNeZero (n + n)))

protected theorem addSelfNeOne : ∀ (n : Nat), n + n ≠ 1
| 0     h := Nat.noConfusion h
| (n+1) h :=
  have h1 : succ (succ (n + n)) = 1, from succAdd n n ▸ h,
  Nat.noConfusion h1 (λ h2, absurd h2 (Nat.succNeZero (n + n)))

protected theorem bit1NeBit0 : ∀ (n m : Nat), bit1 n ≠ bit0 m
| 0     m     h := absurd h (ne.symm (Nat.addSelfNeOne m))
| (n+1) 0     h :=
  have h1 : succ (bit0 (succ n)) = 0, from h,
  absurd h1 (Nat.succNeZero _)
| (n+1) (m+1) h :=
  have h1 : succ (succ (bit1 n)) = succ (succ (bit0 m)), from
    Nat.bit0SuccEq m ▸ Nat.bit1SuccEq n ▸ h,
  have h2 : bit1 n = bit0 m, from
    Nat.noConfusion h1 (λ h2', Nat.noConfusion h2' (λ h2'', h2'')),
  absurd h2 (bit1NeBit0 n m)

protected theorem bit0NeBit1 : ∀ (n m : Nat), bit0 n ≠ bit1 m :=
λ n m : Nat, ne.symm (Nat.bit1NeBit0 m n)

protected theorem bit0Inj : ∀ {n m : Nat}, bit0 n = bit0 m → n = m
| 0     0     h := rfl
| 0     (m+1) h := absurd h.symm (succNeZero _)
| (n+1) 0     h := absurd h (succNeZero _)
| (n+1) (m+1) h :=
  have (n+1) + n = (m+1) + m, from Nat.noConfusion h id,
  have n + (n+1) = m + (m+1), from Nat.addComm (m+1) m ▸ Nat.addComm (n+1) n ▸ this,
  have succ (n + n) = succ (m + m), from this,
  have n + n = m + m, from Nat.noConfusion this id,
  have n = m, from bit0Inj this,
  congrArg (+1) this

protected theorem bit1Inj : ∀ {n m : Nat}, bit1 n = bit1 m → n = m :=
λ n m h,
have succ (bit0 n) = succ (bit0 m), from Nat.bit1EqSuccBit0 n ▸ Nat.bit1EqSuccBit0 m ▸ h,
have bit0 n = bit0 m, from Nat.noConfusion this id,
Nat.bit0Inj this

protected theorem bit0Ne {n m : Nat} : n ≠ m → bit0 n ≠ bit0 m :=
λ h₁ h₂, absurd (Nat.bit0Inj h₂) h₁

protected theorem bit1Ne {n m : Nat} : n ≠ m → bit1 n ≠ bit1 m :=
λ h₁ h₂, absurd (Nat.bit1Inj h₂) h₁

protected theorem zeroNeBit0 {n : Nat} : n ≠ 0 → 0 ≠ bit0 n :=
λ h, ne.symm (Nat.bit0NeZero h)

protected theorem zeroNeBit1 (n : Nat) : 0 ≠ bit1 n :=
ne.symm (Nat.bit1NeZero n)

protected theorem oneNeBit0 (n : Nat) : 1 ≠ bit0 n :=
ne.symm (Nat.bit0NeOne n)

protected theorem oneNeBit1 {n : Nat} : n ≠ 0 → 1 ≠ bit1 n :=
λ h, ne.symm (Nat.bit1NeOne h)

protected theorem oneLtBit1 : ∀ {n : Nat}, n ≠ 0 → 1 < bit1 n
| 0        h := absurd rfl h
| (succ n) h :=
  suffices succ 0 < succ (succ (bit1 n)), from
    (Nat.bit1SuccEq n).symm ▸ this,
  succLtSucc (zeroLtSucc _)

protected theorem oneLtBit0 : ∀ {n : Nat}, n ≠ 0 → 1 < bit0 n
| 0        h := absurd rfl h
| (succ n) h :=
  suffices succ 0 < succ (succ (bit0 n)), from
    (Nat.bit0SuccEq n).symm ▸ this,
  succLtSucc (zeroLtSucc _)

protected theorem bit0Lt {n m : Nat} (h : n < m) : bit0 n < bit0 m :=
Nat.addLtAdd h h

protected theorem bit1Lt {n m : Nat} (h : n < m) : bit1 n < bit1 m :=
succLtSucc (Nat.addLtAdd h h)

protected theorem bit0LtBit1 {n m : Nat} (h : n ≤ m) : bit0 n < bit1 m :=
ltSuccOfLe (Nat.addLeAdd h h)

protected theorem bit1LtBit0 : ∀ {n m : Nat}, n < m → bit1 n < bit0 m
| n 0        h := absurd h (notLtZero _)
| n (succ m) h :=
  have n ≤ m, from leOfLtSucc h,
  have succ (n + n) ≤ succ (m + m),      from succLeSucc (addLeAdd this this),
  have succ (n + n) ≤ succ m + m,        from (succAdd m m).symm ▸ this,
  show succ (n + n) < succ (succ m + m), from ltSuccOfLe this

protected theorem oneLeBit1 (n : Nat) : 1 ≤ bit1 n :=
show 1 ≤ succ (bit0 n), from
succLeSucc (zeroLe (bit0 n))

protected theorem oneLeBit0 : ∀ (n : Nat), n ≠ 0 → 1 ≤ bit0 n
| 0     h := absurd rfl h
| (n+1) h :=
  suffices 1 ≤ succ (succ (bit0 n)), from
    Eq.symm (Nat.bit0SuccEq n) ▸ this,
  succLeSucc (zeroLe (succ (bit0 n)))

/- mul + order -/

theorem mulLeMulLeft {n m : Nat} (k : Nat) (h : n ≤ m) : k * n ≤ k * m :=
match le.dest h with
| ⟨l, hl⟩ :=
  have k * n + k * l = k * m, from Nat.leftDistrib k n l ▸ hl.symm ▸ rfl,
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
have h : 0 * m < n * m, from Nat.mulLtMulOfPosRight ha hb,
Nat.zeroMul m ▸ h

/- power -/

theorem powSucc (n m : Nat) : n^(succ m) = n^m * n :=
rfl

theorem powZero (n : Nat) : n^0 = 1 := rfl

theorem powLePowOfLeLeft {n m : Nat} (h : n ≤ m) : ∀ i : Nat, n^i ≤ m^i
| 0        := Nat.leRefl _
| (succ i) := Nat.mulLeMul (powLePowOfLeLeft i) h

theorem powLePowOfLeRight {n : Nat} (hx : n > 0) {i : Nat} : ∀ {j}, i ≤ j → n^i ≤ n^j
| 0        h :=
  have i = 0, from eqZeroOfLeZero h,
  this.symm ▸ Nat.leRefl _
| (succ j) h :=
  Or.elim (ltOrEqOrLeSucc h)
    (λ h, show n^i ≤ n^j * n, from
          suffices n^i * 1 ≤ n^j * n, from Nat.mulOne (n^i) ▸ this,
          Nat.mulLeMul (powLePowOfLeRight h) hx)
    (λ h, h.symm ▸ Nat.leRefl _)

theorem posPowOfPos {n : Nat} (m : Nat) (h : 0 < n) : 0 < n^m :=
powLePowOfLeRight h (Nat.zeroLe _)

/- Max -/

protected def max (n m : Nat) : Nat :=
if n ≤ m then m else n

end Nat
