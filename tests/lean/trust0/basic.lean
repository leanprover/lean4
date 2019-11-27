/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura
-/
prelude
import Init.Core

notation `ℕ` := Nat

namespace Nat

inductive lessThanOrEqual (a : ℕ) : ℕ → Prop
| refl : lessThanOrEqual a
| step : ∀ {b}, lessThanOrEqual b → lessThanOrEqual (succ b)

@[elabAsEliminator]
theorem lessThanOrEqual.ndrec  {a : Nat} {C : Nat → Prop} (m₁ : C a) (m₂ : ∀ (b : Nat), lessThanOrEqual a b → C b → C (succ b)) {b : ℕ} (h : lessThanOrEqual a b) : C b :=
@lessThanOrEqual.rec a (fun b _ => C b) m₁ m₂ b h

@[elabAsEliminator]
theorem lessThanOrEqual.ndrecOn {a : Nat} {C : Nat → Prop} {b : ℕ} (h : lessThanOrEqual a b) (m₁ : C a) (m₂ : ∀ (b : Nat), lessThanOrEqual a b → C b → C (succ b)) : C b :=
@lessThanOrEqual.rec a (fun b _ => C b) m₁ m₂ b h

instance : HasLessEq ℕ :=
⟨Nat.lessThanOrEqual⟩

@[reducible] protected def le (n m : ℕ) := Nat.lessThanOrEqual n m
@[reducible] protected def lt (n m : ℕ) := Nat.lessThanOrEqual (succ n) m

set_option codegen false


instance : HasLess ℕ :=
⟨Nat.lt⟩

def pred : ℕ → ℕ
| 0     => 0
| a+1   => a

protected def sub : ℕ → ℕ → ℕ
| a, 0     => a
| a, b+1   => pred (sub a b)

protected def mul : Nat → Nat → Nat
| a, 0     => 0
| a, b+1   => (mul a b) + a

instance : HasSub ℕ :=
⟨Nat.sub⟩

instance : HasMul ℕ :=
⟨Nat.mul⟩

def hasDecEq : ∀ (a b : Nat), Decidable (a = b)
| zero,     zero     => isTrue rfl
| succ x,   zero     => isFalse (fun h => Nat.noConfusion h)
| zero,     succ y   => isFalse (fun h => Nat.noConfusion h)
| succ x,   succ y   =>
    match hasDecEq x y with
    | isTrue xeqy => isTrue (xeqy ▸ Eq.refl (succ x))
    | isFalse xney => isFalse (fun h => Nat.noConfusion h (fun xeqy => absurd xeqy xney))

instance : DecidableEq ℕ :=
hasDecEq

def repeat.{u} {α : Type u} (f : ℕ → α → α) : ℕ → α → α
| 0,         a => a
| succ n,    a => f n (repeat n a)

theorem natZeroEqZero : Nat.zero = 0 :=
rfl

/- properties of inequality -/

protected def leRefl : ∀ (a : ℕ), a ≤ a :=
lessThanOrEqual.refl

theorem leSucc (n : ℕ) : n ≤ succ n :=
lessThanOrEqual.step (Nat.leRefl n)

theorem succLeSucc {n m : ℕ} : n ≤ m → succ n ≤ succ m :=
fun h => lessThanOrEqual.ndrec (Nat.leRefl (succ n)) (fun a b => lessThanOrEqual.step) h

theorem zeroLe : ∀ (n : ℕ), 0 ≤ n
| 0     => Nat.leRefl 0
| n+1   => lessThanOrEqual.step (zeroLe n)

theorem zeroLtSucc (n : ℕ) : 0 < succ n :=
succLeSucc (zeroLe n)

def succPos := zeroLtSucc

theorem notSuccLeZero (n : ℕ) (h : succ n ≤ 0) : False :=
nomatch h

theorem notLtZero (a : ℕ) : ¬ a < 0 := notSuccLeZero a

theorem predLePred {n m : ℕ} : n ≤ m → pred n ≤ pred m :=
fun h => lessThanOrEqual.ndrecOn h
  (Nat.leRefl (pred n))
  (fun n => Nat.rec (fun a b => b) (fun a b c => lessThanOrEqual.step) n)

theorem leOfSuccLeSucc {n m : ℕ} : succ n ≤ succ m → n ≤ m :=
predLePred

instance decidableLe : ∀ (a b : ℕ), Decidable (a ≤ b)
| 0,     b     => isTrue (zeroLe b)
| a+1,   0     => isFalse (notSuccLeZero a)
| a+1,   b+1   =>
  match decidableLe a b with
  | isTrue h  => isTrue (succLeSucc h)
  | isFalse h => isFalse (fun a => h (leOfSuccLeSucc a))

instance decidableLt : ∀ (a b : ℕ), Decidable (a < b) :=
fun a b => Nat.decidableLe (succ a) b

protected theorem eqOrLtOfLe {a b : ℕ} (h : a ≤ b) : a = b ∨ a < b :=
lessThanOrEqual.casesOn h (Or.inl rfl) (fun n h => Or.inr (succLeSucc h))

theorem ltSuccOfLe {a b : ℕ} : a ≤ b → a < succ b :=
succLeSucc

theorem succSubSuccEqSub (a b : ℕ) : succ a - succ b = a - b :=
Nat.recOn b
  (show succ a - succ zero = a - zero from (Eq.refl (succ a - succ zero)))
  (fun b => congrArg pred)

theorem notSuccLeSelf : ∀ (n : ℕ), ¬succ n ≤ n :=
fun n => Nat.rec (notSuccLeZero 0) (fun a b c => b (leOfSuccLeSucc c)) n

protected theorem ltIrrefl (n : ℕ) : ¬n < n :=
notSuccLeSelf n

protected theorem leTrans {n m k : ℕ} (h1 : n ≤ m) : m ≤ k → n ≤ k :=
lessThanOrEqual.ndrec h1 (fun p h2 => lessThanOrEqual.step)

theorem predLe : ∀ (n : ℕ), pred n ≤ n
| 0        => lessThanOrEqual.refl 0
| succ a   => lessThanOrEqual.step (lessThanOrEqual.refl a)

theorem predLt : ∀ {n : ℕ}, n ≠ 0 → pred n < n
| 0,        h => absurd rfl h
| succ a,   h => ltSuccOfLe (lessThanOrEqual.refl _)

theorem subLe (a b : ℕ) : a - b ≤ a :=
Nat.recOn b (Nat.leRefl (a - 0)) (fun b₁ => Nat.leTrans (predLe (a - b₁)))

theorem subLt : ∀ {a b : ℕ}, 0 < a → 0 < b → a - b < a
| 0,     b,     h1, h2 => absurd h1 (Nat.ltIrrefl 0)
| a+1,   0,     h1, h2 => absurd h2 (Nat.ltIrrefl 0)
| a+1,   b+1,   h1, h2 =>
  Eq.symm (succSubSuccEqSub a b) ▸
    show a - b < succ a from
    ltSuccOfLe (subLe a b)

protected theorem ltOfLtOfLe {n m k : ℕ} : n < m → m ≤ k → n < k :=
Nat.leTrans

end Nat
