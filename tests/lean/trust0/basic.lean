/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura
-/
prelude
import init.core

notation `ℕ` := Nat

namespace Nat

inductive lessThanOrEqual (a : ℕ) : ℕ → Prop
| refl : lessThanOrEqual a
| step : Π {b}, lessThanOrEqual b → lessThanOrEqual (succ b)

@[elabAsEliminator]
theorem lessThanOrEqual.ndrec  {a : Nat} {C : Nat → Prop} (m₁ : C a) (m₂ : ∀ (b : Nat), lessThanOrEqual a b → C b → C (succ b)) {b : ℕ} (h : lessThanOrEqual a b) : C b :=
@lessThanOrEqual.rec a (λ b _, C b) m₁ m₂ b h

@[elabAsEliminator]
theorem lessThanOrEqual.ndrecOn {a : Nat} {C : Nat → Prop} {b : ℕ} (h : lessThanOrEqual a b) (m₁ : C a) (m₂ : ∀ (b : Nat), lessThanOrEqual a b → C b → C (succ b)) : C b :=
@lessThanOrEqual.rec a (λ b _, C b) m₁ m₂ b h

instance : HasLe ℕ :=
⟨Nat.lessThanOrEqual⟩

@[reducible] protected def le (n m : ℕ) := Nat.lessThanOrEqual n m
@[reducible] protected def lt (n m : ℕ) := Nat.lessThanOrEqual (succ n) m

set_option codegen false


instance : HasLt ℕ :=
⟨Nat.lt⟩

def pred : ℕ → ℕ
| 0     := 0
| (a+1) := a

protected def sub : ℕ → ℕ → ℕ
| a 0     := a
| a (b+1) := pred (sub a b)

protected def mul : Nat → Nat → Nat
| a 0     := 0
| a (b+1) := (mul a b) + a

instance : HasSub ℕ :=
⟨Nat.sub⟩

instance : HasMul ℕ :=
⟨Nat.mul⟩

def hasDecEq : Π a b : Nat, Decidable (a = b)
| zero     zero     := isTrue rfl
| (succ x) zero     := isFalse (λ h, Nat.noConfusion h)
| zero     (succ y) := isFalse (λ h, Nat.noConfusion h)
| (succ x) (succ y) :=
    match hasDecEq x y with
    | isTrue xeqy := isTrue (xeqy ▸ Eq.refl (succ x))
    | isFalse xney := isFalse (λ h, Nat.noConfusion h (λ xeqy, absurd xeqy xney))

instance : DecidableEq ℕ :=
{decEq := hasDecEq}

def {u} repeat {α : Type u} (f : ℕ → α → α) : ℕ → α → α
| 0         a := a
| (succ n)  a := f n (repeat n a)

lemma natZeroEqZero : Nat.zero = 0 :=
rfl

/- properties of inequality -/

protected def leRefl : ∀ a : ℕ, a ≤ a :=
lessThanOrEqual.refl

lemma leSucc (n : ℕ) : n ≤ succ n :=
lessThanOrEqual.step (Nat.leRefl n)

lemma succLeSucc {n m : ℕ} : n ≤ m → succ n ≤ succ m :=
λ h, lessThanOrEqual.ndrec (Nat.leRefl (succ n)) (λ a b, lessThanOrEqual.step) h

lemma zeroLe : ∀ (n : ℕ), 0 ≤ n
| 0     := Nat.leRefl 0
| (n+1) := lessThanOrEqual.step (zeroLe n)

lemma zeroLtSucc (n : ℕ) : 0 < succ n :=
succLeSucc (zeroLe n)

def succPos := zeroLtSucc

lemma notSuccLeZero : ∀ (n : ℕ), succ n ≤ 0 → False
.

lemma notLtZero (a : ℕ) : ¬ a < 0 := notSuccLeZero a

lemma predLePred {n m : ℕ} : n ≤ m → pred n ≤ pred m :=
λ h, lessThanOrEqual.ndrecOn h
  (Nat.leRefl (pred n))
  (λ n, Nat.rec (λ a b, b) (λ a b c, lessThanOrEqual.step) n)

lemma leOfSuccLeSucc {n m : ℕ} : succ n ≤ succ m → n ≤ m :=
predLePred

instance decidableLe : ∀ a b : ℕ, Decidable (a ≤ b)
| 0     b     := isTrue (zeroLe b)
| (a+1) 0     := isFalse (notSuccLeZero a)
| (a+1) (b+1) :=
  match decidableLe a b with
  | isTrue h  := isTrue (succLeSucc h)
  | isFalse h := isFalse (λ a, h (leOfSuccLeSucc a))

instance decidableLt : ∀ a b : ℕ, Decidable (a < b) :=
λ a b, Nat.decidableLe (succ a) b

protected lemma eqOrLtOfLe {a b : ℕ} (h : a ≤ b) : a = b ∨ a < b :=
lessThanOrEqual.casesOn h (Or.inl rfl) (λ n h, Or.inr (succLeSucc h))

lemma ltSuccOfLe {a b : ℕ} : a ≤ b → a < succ b :=
succLeSucc

lemma succSubSuccEqSub (a b : ℕ) : succ a - succ b = a - b :=
Nat.recOn b
  (show succ a - succ zero = a - zero, from (Eq.refl (succ a - succ zero)))
  (λ b, congrArg pred)

lemma notSuccLeSelf : ∀ n : ℕ, ¬succ n ≤ n :=
λ n, Nat.rec (notSuccLeZero 0) (λ a b c, b (leOfSuccLeSucc c)) n

protected lemma ltIrrefl (n : ℕ) : ¬n < n :=
notSuccLeSelf n

protected lemma leTrans {n m k : ℕ} (h1 : n ≤ m) : m ≤ k → n ≤ k :=
lessThanOrEqual.ndrec h1 (λ p h2, lessThanOrEqual.step)

lemma predLe : ∀ (n : ℕ), pred n ≤ n
| 0        := lessThanOrEqual.refl 0
| (succ a) := lessThanOrEqual.step (lessThanOrEqual.refl a)

lemma predLt : ∀ {n : ℕ}, n ≠ 0 → pred n < n
| 0        h := absurd rfl h
| (succ a) h := ltSuccOfLe (lessThanOrEqual.refl _)

lemma subLe (a b : ℕ) : a - b ≤ a :=
Nat.recOn b (Nat.leRefl (a - 0)) (λ b₁, Nat.leTrans (predLe (a - b₁)))

lemma subLt : ∀ {a b : ℕ}, 0 < a → 0 < b → a - b < a
| 0     b     h1 h2 := absurd h1 (Nat.ltIrrefl 0)
| (a+1) 0     h1 h2 := absurd h2 (Nat.ltIrrefl 0)
| (a+1) (b+1) h1 h2 :=
  Eq.symm (succSubSuccEqSub a b) ▸
    show a - b < succ a, from
    ltSuccOfLe (subLe a b)

protected lemma ltOfLtOfLe {n m k : ℕ} : n < m → m ≤ k → n < k :=
Nat.leTrans

end Nat
