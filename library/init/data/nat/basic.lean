/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura
-/
prelude
import init.core
universes u

notation `ℕ` := nat

namespace nat

@[extern cpp "lean::nat_dec_eq"]
def beq : nat → nat → bool
| zero     zero     := tt
| zero     (succ m) := ff
| (succ n) zero     := ff
| (succ n) (succ m) := beq n m

theorem eqOfBeqEqTt : ∀ {n m : nat}, beq n m = tt → n = m
| zero     zero     h := rfl
| zero     (succ m) h := bool.noConfusion h
| (succ n) zero     h := bool.noConfusion h
| (succ n) (succ m) h :=
  have beq n m = tt, from h,
  have n = m, from eqOfBeqEqTt this,
  congrArg succ this

theorem neOfBeqEqFf : ∀ {n m : nat}, beq n m = ff → n ≠ m
| zero     zero     h₁ h₂ := bool.noConfusion h₁
| zero     (succ m) h₁ h₂ := nat.noConfusion h₂
| (succ n) zero     h₁ h₂ := nat.noConfusion h₂
| (succ n) (succ m) h₁ h₂ :=
  have beq n m = ff, from h₁,
  have n ≠ m, from neOfBeqEqFf this,
  nat.noConfusion h₂ (λ h₂, absurd h₂ this)

@[extern cpp "lean::nat_dec_eq"]
protected def decEq (n m : @& nat) : decidable (n = m) :=
if h : beq n m = tt then isTrue (eqOfBeqEqTt h)
else isFalse (neOfBeqEqFf (eqFfOfNeTt h))

@[inline] instance : decidableEq nat :=
{decEq := nat.decEq}

@[extern cpp "lean::nat_dec_le"]
def ble : nat → nat → bool
| zero     zero     := tt
| zero     (succ m) := tt
| (succ n) zero     := ff
| (succ n) (succ m) := ble n m

protected def le (n m : nat) : Prop :=
ble n m = tt

instance : hasLe nat :=
⟨nat.le⟩

protected def lt (n m : nat) : Prop :=
nat.le (succ n) m

instance : hasLt nat :=
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

instance : hasSub nat :=
⟨nat.sub⟩

instance : hasMul nat :=
⟨nat.mul⟩

@[specialize] def repeatCore {α : Type u} (f : nat → α → α) (s : nat) : nat → α → α
| 0         a := a
| (succ n)  a := repeatCore n (f (s - (succ n)) a)

@[inline] def repeat {α : Type u} (f : nat → α → α) (n : nat) (a : α) : α :=
repeatCore f n n a

protected def pow (m : nat) : nat → nat
| 0        := 1
| (succ n) := pow n * m

instance : hasPow nat nat :=
⟨nat.pow⟩

/- nat.add theorems -/

protected theorem zeroAdd : ∀ n : nat, 0 + n = n
| 0     := rfl
| (n+1) := congrArg succ (zeroAdd n)

theorem succAdd : ∀ n m : nat, (succ n) + m = succ (n + m)
| n 0     := rfl
| n (m+1) := congrArg succ (succAdd n m)

theorem addSucc (n m : nat) : n + succ m = succ (n + m) :=
rfl

protected theorem addZero (n : nat) : n + 0 = n :=
rfl

theorem addOne (n : nat) : n + 1 = succ n :=
rfl

theorem succEqAddOne (n : nat) : succ n = n + 1 :=
rfl

protected theorem addComm : ∀ n m : nat, n + m = m + n
| n 0     := eq.symm (nat.zeroAdd n)
| n (m+1) :=
  suffices succ (n + m) = succ (m + n), from
    eq.symm (succAdd m n) ▸ this,
  congrArg succ (addComm n m)

protected theorem addAssoc : ∀ n m k : nat, (n + m) + k = n + (m + k)
| n m 0        := rfl
| n m (succ k) := congrArg succ (addAssoc n m k)

protected theorem addLeftComm : ∀ (n m k : nat), n + (m + k) = m + (n + k) :=
leftComm nat.add nat.addComm nat.addAssoc

protected theorem addRightComm : ∀ (n m k : nat), (n + m) + k = (n + k) + m :=
rightComm nat.add nat.addComm nat.addAssoc

protected theorem addLeftCancel : ∀ {n m k : nat}, n + m = n + k → m = k
| 0        m k h := nat.zeroAdd m ▸ nat.zeroAdd k ▸ h
| (succ n) m k h :=
  have n+m = n+k, from
    have succ (n + m) = succ (n + k), from succAdd n m ▸ succAdd n k ▸ h,
    nat.noConfusion this id,
  addLeftCancel this

protected theorem addRightCancel {n m k : nat} (h : n + m = k + m) : n = k :=
have m + n = m + k, from nat.addComm n m ▸ nat.addComm k m ▸ h,
nat.addLeftCancel this

/- nat.mul theorems -/

protected theorem mulZero (n : nat) : n * 0 = 0 :=
rfl

theorem mulSucc (n m : nat) : n * succ m = n * m + n :=
rfl

protected theorem zeroMul : ∀ (n : nat), 0 * n = 0
| 0        := rfl
| (succ n) := (mulSucc 0 n).symm ▸ (zeroMul n).symm ▸ rfl

theorem succMul : ∀ (n m : nat), (succ n) * m = (n * m) + m
| n 0        := rfl
| n (succ m) :=
  have succ (n * m + m + n) = succ (n * m + n + m), from
    congrArg succ (nat.addRightComm _ _ _),
  (mulSucc n m).symm ▸ (mulSucc (succ n) m).symm ▸ (succMul n m).symm ▸ this

protected theorem mulComm : ∀ (n m : nat), n * m = m * n
| n 0        := (nat.zeroMul n).symm ▸ (nat.mulZero n).symm ▸ rfl
| n (succ m) := (mulSucc n m).symm ▸ (succMul m n).symm ▸ (mulComm n m).symm ▸ rfl

protected theorem mulOne : ∀ (n : nat), n * 1 = n :=
nat.zeroAdd

protected theorem oneMul (n : nat) : 1 * n = n :=
nat.mulComm n 1 ▸ nat.mulOne n

local infix `◾`:50 := eq.trans

protected theorem leftDistrib : ∀ (n m k : nat), n * (m + k) = n * m + n * k
| 0        m k := (nat.zeroMul (m + k)).symm ▸ (nat.zeroMul m).symm ▸ (nat.zeroMul k).symm ▸ rfl
| (succ n) m k :=
  have h₁ : succ n * (m + k) = n * (m + k) + (m + k),              from succMul _ _,
  have h₂ : n * (m + k) + (m + k) = (n * m + n * k) + (m + k),     from leftDistrib n m k ▸ rfl,
  have h₃ : (n * m + n * k) + (m + k) = n * m + (n * k + (m + k)), from nat.addAssoc _ _ _,
  have h₄ : n * m + (n * k + (m + k)) = n * m + (m + (n * k + k)), from congrArg (λ x, n*m + x) (nat.addLeftComm _ _ _),
  have h₅ : n * m + (m + (n * k + k)) = (n * m + m) + (n * k + k), from (nat.addAssoc _ _ _).symm,
  have h₆ : (n * m + m) + (n * k + k) = (n * m + m) + succ n * k,  from succMul n k ▸ rfl,
  have h₇ : (n * m + m) + succ n * k = succ n * m + succ n * k,    from succMul n m ▸ rfl,
  h₁ ◾ h₂ ◾ h₃ ◾ h₄ ◾ h₅ ◾ h₆ ◾ h₇

protected theorem rightDistrib (n m k : nat) : (n + m) * k = n * k + m * k :=
have h₁ : (n + m) * k = k * (n + m),     from nat.mulComm _ _,
have h₂ : k * (n + m) = k * n + k * m,   from nat.leftDistrib _ _ _,
have h₃ : k * n + k * m = n * k + k * m, from nat.mulComm n k ▸ rfl,
have h₄ : n * k + k * m = n * k + m * k, from nat.mulComm m k ▸ rfl,
h₁ ◾ h₂ ◾ h₃ ◾ h₄

protected theorem mulAssoc : ∀ (n m k : nat), (n * m) * k = n * (m * k)
| n m 0        := rfl
| n m (succ k) :=
  have h₁ : n * m * succ k = n * m * (k + 1),              from rfl,
  have h₂ : n * m * (k + 1) = (n * m * k) + n * m * 1,     from nat.leftDistrib _ _ _,
  have h₃ : (n * m * k) + n * m * 1 = (n * m * k) + n * m, from (nat.mulOne (n*m)).symm ▸ rfl,
  have h₄ : (n * m * k) + n * m = (n * (m * k)) + n * m,   from (mulAssoc n m k).symm ▸ rfl,
  have h₅ : (n * (m * k)) + n * m = n * (m * k + m),       from (nat.leftDistrib n (m*k) m).symm,
  have h₆ : n * (m * k + m) = n * (m * succ k),            from nat.mulSucc m k ▸ rfl,
h₁ ◾ h₂ ◾ h₃ ◾ h₄ ◾ h₅ ◾ h₆

/- Inequalities -/

protected def leRefl : ∀ n : nat, n ≤ n
| zero     := rfl
| (succ n) := leRefl n

theorem leSucc : ∀ (n : nat), n ≤ succ n
| zero     := rfl
| (succ n) := leSucc n

theorem succLeSucc {n m : nat} (h : n ≤ m) : succ n ≤ succ m :=
h

theorem succLtSucc {n m : nat} : n < m → succ n < succ m :=
succLeSucc

theorem leStep : ∀ {n m : nat}, n ≤ m → n ≤ succ m
| zero     zero     h := rfl
| zero     (succ n) h := rfl
| (succ n) zero     h := bool.noConfusion h
| (succ n) (succ m) h :=
  have n ≤ m, from h,
  have n ≤ succ m, from leStep this,
  succLeSucc this

theorem zeroLe : ∀ (n : nat), 0 ≤ n
| zero     := rfl
| (succ n) := rfl

theorem zeroLtSucc (n : nat) : 0 < succ n :=
succLeSucc (zeroLe n)

def succPos := zeroLtSucc

theorem notSuccLeZero : ∀ (n : nat), succ n ≤ 0 → false
.

theorem notLtZero (n : nat) : ¬ n < 0 :=
notSuccLeZero n

theorem predLePred : ∀ {n m : nat}, n ≤ m → pred n ≤ pred m
| zero     zero     h := rfl
| zero     (succ n) h := zeroLe n
| (succ n) zero     h := bool.noConfusion h
| (succ n) (succ m) h := h

theorem leOfSuccLeSucc {n m : nat} : succ n ≤ succ m → n ≤ m :=
predLePred

@[extern cpp "lean::nat_dec_le"]
instance decLe (n m : @& nat) : decidable (n ≤ m) :=
decEq (ble n m) tt

@[extern cpp "lean::nat_dec_lt"]
instance decLt (n m : @& nat) : decidable (n < m) :=
nat.decLe (succ n) m

protected theorem eqOrLtOfLe : ∀ {n m: nat}, n ≤ m → n = m ∨ n < m
| zero     zero     h := or.inl rfl
| zero     (succ n) h := or.inr $ zeroLe n
| (succ n) zero     h := bool.noConfusion h
| (succ n) (succ m) h :=
  have n ≤ m, from h,
  have n = m ∨ n < m, from eqOrLtOfLe this,
  or.elim this
   (λ h, or.inl $ congrArg succ h)
   (λ h, or.inr $ succLtSucc h)

theorem ltSuccOfLe {n m : nat} : n ≤ m → n < succ m :=
succLeSucc

protected theorem subZero (n : nat) : n - 0 = n :=
rfl

theorem succSubSuccEqSub (n m : nat) : succ n - succ m = n - m :=
nat.recOn m
  (show succ n - succ zero = n - zero, from (eq.refl (succ n - succ zero)))
  (λ m, congrArg pred)

theorem notSuccLeSelf : ∀ n : nat, ¬succ n ≤ n :=
λ n, nat.rec (notSuccLeZero 0) (λ a b c, b (leOfSuccLeSucc c)) n

protected theorem ltIrrefl (n : nat) : ¬n < n :=
notSuccLeSelf n

protected theorem leTrans : ∀ {n m k : nat}, n ≤ m → m ≤ k → n ≤ k
| zero     m        k        h₁ h₂ := zeroLe _
| (succ n) zero     k        h₁ h₂ := bool.noConfusion h₁
| (succ n) (succ m) zero     h₁ h₂ := bool.noConfusion h₂
| (succ n) (succ m) (succ k) h₁ h₂ :=
  have h₁' : n ≤ m, from h₁,
  have h₂' : m ≤ k, from h₂,
  have n ≤ k, from leTrans h₁' h₂',
  succLeSucc this

theorem predLe : ∀ (n : nat), pred n ≤ n
| zero     := rfl
| (succ n) := leSucc _

theorem predLt : ∀ {n : nat}, n ≠ 0 → pred n < n
| zero     h := absurd rfl h
| (succ n) h := ltSuccOfLe (nat.leRefl _)

theorem subLe (n m : nat) : n - m ≤ n :=
nat.recOn m (nat.leRefl (n - 0)) (λ m, nat.leTrans (predLe (n - m)))

theorem subLt : ∀ {n m : nat}, 0 < n → 0 < m → n - m < n
| 0     m     h1 h2 := absurd h1 (nat.ltIrrefl 0)
| (n+1) 0     h1 h2 := absurd h2 (nat.ltIrrefl 0)
| (n+1) (m+1) h1 h2 :=
  eq.symm (succSubSuccEqSub n m) ▸
    show n - m < succ n, from
    ltSuccOfLe (subLe n m)

protected theorem ltOfLtOfLe {n m k : nat} : n < m → m ≤ k → n < k :=
nat.leTrans

protected theorem leOfEq {n m : nat} (p : n = m) : n ≤ m :=
p ▸ nat.leRefl n

theorem leSuccOfLe {n m : nat} (h : n ≤ m) : n ≤ succ m :=
nat.leTrans h (leSucc m)

theorem leOfSuccLe {n m : nat} (h : succ n ≤ m) : n ≤ m :=
nat.leTrans (leSucc n) h

protected theorem leOfLt {n m : nat} (h : n < m) : n ≤ m :=
leOfSuccLe h

def lt.step {n m : nat} : n < m → n < succ m := leStep

theorem eqZeroOrPos : ∀ (n : nat), n = 0 ∨ n > 0
| 0     := or.inl rfl
| (n+1) := or.inr (succPos _)

protected theorem ltTrans {n m k : nat} (h₁ : n < m) : m < k → n < k :=
nat.leTrans (leStep h₁)

protected theorem ltOfLeOfLt {n m k : nat} (h₁ : n ≤ m) : m < k → n < k :=
nat.leTrans (succLeSucc h₁)

def lt.base (n : nat) : n < succ n := nat.leRefl (succ n)

theorem ltSuccSelf (n : nat) : n < succ n := lt.base n

protected theorem leAntisymm : ∀ {n m : nat}, n ≤ m → m ≤ n → n = m
| zero     zero     h₁ h₂ := rfl
| (succ n) zero     h₁ h₂ := bool.noConfusion h₁
| zero     (succ m) h₁ h₂ := bool.noConfusion h₂
| (succ n) (succ m) h₁ h₂ :=
  have h₁' : n ≤ m, from h₁,
  have h₂' : m ≤ n, from h₂,
  have n = m, from leAntisymm h₁' h₂',
  congrArg succ this

protected theorem ltOrGe : ∀ (n m : nat), n < m ∨ n ≥ m
| n 0     := or.inr (zeroLe n)
| n (m+1) :=
  match ltOrGe n m with
  | or.inl h := or.inl (leSuccOfLe h)
  | or.inr h :=
    match nat.eqOrLtOfLe h with
    | or.inl h1 := or.inl (h1 ▸ ltSuccSelf m)
    | or.inr h1 := or.inr h1

protected theorem leTotal (m n : nat) : m ≤ n ∨ n ≤ m :=
or.elim (nat.ltOrGe m n)
  (λ h, or.inl (nat.leOfLt h))
  or.inr

protected theorem ltOfLeAndNe {m n : nat} (h1 : m ≤ n) : m ≠ n → m < n :=
resolveRight (or.swap (nat.eqOrLtOfLe h1))

theorem eqZeroOfLeZero {n : nat} (h : n ≤ 0) : n = 0 :=
nat.leAntisymm h (zeroLe _)

theorem ltOfSuccLt {n m : nat} : succ n < m → n < m :=
leOfSuccLe

theorem ltOfSuccLtSucc {n m : nat} : succ n < succ m → n < m :=
leOfSuccLeSucc

theorem ltOfSuccLe {n m : nat} (h : succ n ≤ m) : n < m :=
h

theorem succLeOfLt {n m : nat} (h : n < m) : succ n ≤ m :=
h

theorem ltOrEqOrLeSucc {m n : nat} (h : m ≤ succ n) : m ≤ n ∨ m = succ n :=
decidable.byCases
  (λ h' : m = succ n, or.inr h')
  (λ h' : m ≠ succ n,
     have m < succ n, from nat.ltOfLeAndNe h h',
     have succ m ≤ succ n, from succLeOfLt this,
     or.inl (leOfSuccLeSucc this))

theorem leAddRight : ∀ (n k : nat), n ≤ n + k
| n 0     := nat.leRefl n
| n (k+1) := leSuccOfLe (leAddRight n k)

theorem leAddLeft (n m : nat): n ≤ m + n :=
nat.addComm n m ▸ leAddRight n m

theorem le.dest : ∀ {n m : nat}, n ≤ m → ∃ k, n + k = m
| zero     zero     h := ⟨0, rfl⟩
| zero     (succ n) h := ⟨succ n, show 0 + succ n = succ n, from (nat.addComm 0 (succ n)).symm ▸ rfl⟩
| (succ n) zero     h := bool.noConfusion h
| (succ n) (succ m) h :=
  have n ≤ m, from h,
  have ∃ k, n + k = m, from le.dest this,
  match this with
  | ⟨k, h⟩ := ⟨k, show succ n + k = succ m, from ((succAdd n k).symm ▸ h ▸ rfl)⟩

theorem le.intro {n m k : nat} (h : n + k = m) : n ≤ m :=
h ▸ leAddRight n k

protected theorem notLeOfGt {n m : nat} (h : n > m) : ¬ n ≤ m :=
λ h₁, or.elim (nat.ltOrGe n m)
  (λ h₂, absurd (nat.ltTrans h h₂) (nat.ltIrrefl _))
  (λ h₂, have heq : n = m, from nat.leAntisymm h₁ h₂, absurd (@eq.subst _ _ _ _ heq h) (nat.ltIrrefl m))

theorem gtOfNotLe {n m : nat} (h : ¬ n ≤ m) : n > m :=
or.elim (nat.ltOrGe m n)
  (λ h₁, h₁)
  (λ h₁, absurd h₁ h)

protected theorem ltOfLeOfNe {n m : nat} (h₁ : n ≤ m) (h₂ : n ≠ m) : n < m :=
or.elim (nat.ltOrGe n m)
  (λ h₃, h₃)
  (λ h₃, absurd (nat.leAntisymm h₁ h₃) h₂)

protected theorem addLeAddLeft {n m : nat} (h : n ≤ m) (k : nat) : k + n ≤ k + m :=
match le.dest h with
| ⟨w, hw⟩ :=
  have h₁ : k + n + w = k + (n + w), from nat.addAssoc _ _ _,
  have h₂ : k + (n + w) = k + m,     from congrArg _ hw,
  le.intro $ h₁ ◾ h₂

protected theorem addLeAddRight {n m : nat} (h : n ≤ m) (k : nat) : n + k ≤ m + k :=
have h₁ : n + k = k + n, from nat.addComm _ _,
have h₂ : k + n ≤ k + m, from nat.addLeAddLeft h k,
have h₃ : k + m = m + k, from nat.addComm _ _,
transRelLeft (≤) (transRelRight (≤) h₁ h₂) h₃

protected theorem addLtAddLeft {n m : nat} (h : n < m) (k : nat) : k + n < k + m :=
ltOfSuccLe (addSucc k n ▸ nat.addLeAddLeft (succLeOfLt h) k)

protected theorem addLtAddRight {n m : nat} (h : n < m) (k : nat) : n + k < m + k :=
nat.addComm k m ▸ nat.addComm k n ▸ nat.addLtAddLeft h k

protected theorem zeroLtOne : 0 < (1:nat) :=
zeroLtSucc 0

theorem leOfLtSucc {m n : nat} : m < succ n → m ≤ n :=
leOfSuccLeSucc

theorem addLeAdd {a b c d : nat} (h₁ : a ≤ b) (h₂ : c ≤ d) : a + c ≤ b + d :=
nat.leTrans (nat.addLeAddRight h₁ c) (nat.addLeAddLeft h₂ b)

theorem addLtAdd {a b c d : nat} (h₁ : a < b) (h₂ : c < d) : a + c < b + d :=
nat.ltTrans (nat.addLtAddRight h₁ c) (nat.addLtAddLeft h₂ b)

/- Basic theorems for comparing numerals -/

theorem natZeroEqZero : nat.zero = 0 :=
rfl

protected theorem oneNeZero : 1 ≠ (0 : nat) :=
assume h, nat.noConfusion h

protected theorem zeroNeOne : 0 ≠ (1 : nat) :=
assume h, nat.noConfusion h

theorem succNeZero (n : nat) : succ n ≠ 0 :=
assume h, nat.noConfusion h

protected theorem bit0SuccEq (n : nat) : bit0 (succ n) = succ (succ (bit0 n)) :=
show succ (succ n + n) = succ (succ (n + n)), from
congrArg succ (succAdd n n)

protected theorem zeroLtBit0 : ∀ {n : nat}, n ≠ 0 → 0 < bit0 n
| 0        h := absurd rfl h
| (succ n) h :=
  have h₁ : 0 < succ (succ (bit0 n)),             from zeroLtSucc _,
  have h₂ : succ (succ (bit0 n)) = bit0 (succ n), from (nat.bit0SuccEq n).symm,
  transRelLeft (<) h₁ h₂

protected theorem zeroLtBit1 (n : nat) : 0 < bit1 n :=
zeroLtSucc _

protected theorem bit0NeZero : ∀ {n : nat}, n ≠ 0 → bit0 n ≠ 0
| 0     h := absurd rfl h
| (n+1) h :=
  suffices (n+1) + (n+1) ≠ 0, from this,
  suffices succ ((n+1) + n) ≠ 0, from this,
  λ h, nat.noConfusion h

protected theorem bit1NeZero (n : nat) : bit1 n ≠ 0 :=
show succ (n + n) ≠ 0, from
λ h, nat.noConfusion h

protected theorem bit1EqSuccBit0 (n : nat) : bit1 n = succ (bit0 n) :=
rfl

protected theorem bit1SuccEq (n : nat) : bit1 (succ n) = succ (succ (bit1 n)) :=
eq.trans (nat.bit1EqSuccBit0 (succ n)) (congrArg succ (nat.bit0SuccEq n))

protected theorem bit1NeOne : ∀ {n : nat}, n ≠ 0 → bit1 n ≠ 1
| 0     h h1 := absurd rfl h
| (n+1) h h1 := nat.noConfusion h1 (λ h2, absurd h2 (succNeZero _))

protected theorem bit0NeOne : ∀ n : nat, bit0 n ≠ 1
| 0     h := absurd h (ne.symm nat.oneNeZero)
| (n+1) h :=
  have h1 : succ (succ (n + n)) = 1, from succAdd n n ▸ h,
  nat.noConfusion h1
    (λ h2, absurd h2 (succNeZero (n + n)))

protected theorem addSelfNeOne : ∀ (n : nat), n + n ≠ 1
| 0     h := nat.noConfusion h
| (n+1) h :=
  have h1 : succ (succ (n + n)) = 1, from succAdd n n ▸ h,
  nat.noConfusion h1 (λ h2, absurd h2 (nat.succNeZero (n + n)))

protected theorem bit1NeBit0 : ∀ (n m : nat), bit1 n ≠ bit0 m
| 0     m     h := absurd h (ne.symm (nat.addSelfNeOne m))
| (n+1) 0     h :=
  have h1 : succ (bit0 (succ n)) = 0, from h,
  absurd h1 (nat.succNeZero _)
| (n+1) (m+1) h :=
  have h1 : succ (succ (bit1 n)) = succ (succ (bit0 m)), from
    nat.bit0SuccEq m ▸ nat.bit1SuccEq n ▸ h,
  have h2 : bit1 n = bit0 m, from
    nat.noConfusion h1 (λ h2', nat.noConfusion h2' (λ h2'', h2'')),
  absurd h2 (bit1NeBit0 n m)

protected theorem bit0NeBit1 : ∀ (n m : nat), bit0 n ≠ bit1 m :=
λ n m : nat, ne.symm (nat.bit1NeBit0 m n)

protected theorem bit0Inj : ∀ {n m : nat}, bit0 n = bit0 m → n = m
| 0     0     h := rfl
| 0     (m+1) h := absurd h.symm (succNeZero _)
| (n+1) 0     h := absurd h (succNeZero _)
| (n+1) (m+1) h :=
  have (n+1) + n = (m+1) + m, from nat.noConfusion h id,
  have n + (n+1) = m + (m+1), from nat.addComm (m+1) m ▸ nat.addComm (n+1) n ▸ this,
  have succ (n + n) = succ (m + m), from this,
  have n + n = m + m, from nat.noConfusion this id,
  have n = m, from bit0Inj this,
  congrArg (+1) this

protected theorem bit1Inj : ∀ {n m : nat}, bit1 n = bit1 m → n = m :=
λ n m h,
have succ (bit0 n) = succ (bit0 m), from nat.bit1EqSuccBit0 n ▸ nat.bit1EqSuccBit0 m ▸ h,
have bit0 n = bit0 m, from nat.noConfusion this id,
nat.bit0Inj this

protected theorem bit0Ne {n m : nat} : n ≠ m → bit0 n ≠ bit0 m :=
λ h₁ h₂, absurd (nat.bit0Inj h₂) h₁

protected theorem bit1Ne {n m : nat} : n ≠ m → bit1 n ≠ bit1 m :=
λ h₁ h₂, absurd (nat.bit1Inj h₂) h₁

protected theorem zeroNeBit0 {n : nat} : n ≠ 0 → 0 ≠ bit0 n :=
λ h, ne.symm (nat.bit0NeZero h)

protected theorem zeroNeBit1 (n : nat) : 0 ≠ bit1 n :=
ne.symm (nat.bit1NeZero n)

protected theorem oneNeBit0 (n : nat) : 1 ≠ bit0 n :=
ne.symm (nat.bit0NeOne n)

protected theorem oneNeBit1 {n : nat} : n ≠ 0 → 1 ≠ bit1 n :=
λ h, ne.symm (nat.bit1NeOne h)

protected theorem oneLtBit1 : ∀ {n : nat}, n ≠ 0 → 1 < bit1 n
| 0        h := absurd rfl h
| (succ n) h :=
  suffices succ 0 < succ (succ (bit1 n)), from
    (nat.bit1SuccEq n).symm ▸ this,
  succLtSucc (zeroLtSucc _)

protected theorem oneLtBit0 : ∀ {n : nat}, n ≠ 0 → 1 < bit0 n
| 0        h := absurd rfl h
| (succ n) h :=
  suffices succ 0 < succ (succ (bit0 n)), from
    (nat.bit0SuccEq n).symm ▸ this,
  succLtSucc (zeroLtSucc _)

protected theorem bit0Lt {n m : nat} (h : n < m) : bit0 n < bit0 m :=
nat.addLtAdd h h

protected theorem bit1Lt {n m : nat} (h : n < m) : bit1 n < bit1 m :=
succLtSucc (nat.addLtAdd h h)

protected theorem bit0LtBit1 {n m : nat} (h : n ≤ m) : bit0 n < bit1 m :=
ltSuccOfLe (nat.addLeAdd h h)

protected theorem bit1LtBit0 : ∀ {n m : nat}, n < m → bit1 n < bit0 m
| n 0        h := absurd h (notLtZero _)
| n (succ m) h :=
  have n ≤ m, from leOfLtSucc h,
  have succ (n + n) ≤ succ (m + m),      from succLeSucc (addLeAdd this this),
  have succ (n + n) ≤ succ m + m,        from (succAdd m m).symm ▸ this,
  show succ (n + n) < succ (succ m + m), from ltSuccOfLe this

protected theorem oneLeBit1 (n : nat) : 1 ≤ bit1 n :=
show 1 ≤ succ (bit0 n), from
succLeSucc (zeroLe (bit0 n))

protected theorem oneLeBit0 : ∀ (n : nat), n ≠ 0 → 1 ≤ bit0 n
| 0     h := absurd rfl h
| (n+1) h :=
  suffices 1 ≤ succ (succ (bit0 n)), from
    eq.symm (nat.bit0SuccEq n) ▸ this,
  succLeSucc (zeroLe (succ (bit0 n)))

/- mul + order -/

theorem mulLeMulLeft {n m : nat} (k : nat) (h : n ≤ m) : k * n ≤ k * m :=
match le.dest h with
| ⟨l, hl⟩ :=
  have k * n + k * l = k * m, from nat.leftDistrib k n l ▸ hl.symm ▸ rfl,
  le.intro this

theorem mulLeMulRight {n m : nat} (k : nat) (h : n ≤ m) : n * k ≤ m * k :=
nat.mulComm k m ▸ nat.mulComm k n ▸ mulLeMulLeft k h

protected theorem mulLeMul {n₁ m₁ n₂ m₂ : nat} (h₁ : n₁ ≤ n₂) (h₂ : m₁ ≤ m₂) : n₁ * m₁ ≤ n₂ * m₂ :=
nat.leTrans (mulLeMulRight _ h₁) (mulLeMulLeft _ h₂)

protected theorem mulLtMulOfPosLeft {n m k : nat} (h : n < m) (hk : k > 0) : k * n < k * m :=
nat.ltOfLtOfLe (nat.addLtAddLeft hk _) (nat.mulSucc k n ▸ nat.mulLeMulLeft k (succLeOfLt h))

protected theorem mulLtMulOfPosRight {n m k : nat} (h : n < m) (hk : k > 0) : n * k < m * k :=
nat.mulComm k m ▸ nat.mulComm k n ▸ nat.mulLtMulOfPosLeft h hk

protected theorem mulPos {n m : nat} (ha : n > 0) (hb : m > 0) : n * m > 0 :=
have h : 0 * m < n * m, from nat.mulLtMulOfPosRight ha hb,
nat.zeroMul m ▸ h

/- power -/

theorem powSucc (n m : nat) : n^(succ m) = n^m * n :=
rfl

theorem powZero (n : nat) : n^0 = 1 := rfl

theorem powLePowOfLeLeft {n m : nat} (h : n ≤ m) : ∀ i : nat, n^i ≤ m^i
| 0        := nat.leRefl _
| (succ i) := nat.mulLeMul (powLePowOfLeLeft i) h

theorem powLePowOfLeRight {n : nat} (hx : n > 0) {i : nat} : ∀ {j}, i ≤ j → n^i ≤ n^j
| 0        h :=
  have i = 0, from eqZeroOfLeZero h,
  this.symm ▸ nat.leRefl _
| (succ j) h :=
  or.elim (ltOrEqOrLeSucc h)
    (λ h, show n^i ≤ n^j * n, from
          suffices n^i * 1 ≤ n^j * n, from nat.mulOne (n^i) ▸ this,
          nat.mulLeMul (powLePowOfLeRight h) hx)
    (λ h, h.symm ▸ nat.leRefl _)

theorem posPowOfPos {n : nat} (m : nat) (h : 0 < n) : 0 < n^m :=
powLePowOfLeRight h (nat.zeroLe _)

/- Max -/

protected def max (n m : nat) : nat :=
if n ≤ m then m else n

end nat
