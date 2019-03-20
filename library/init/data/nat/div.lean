/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.wf init.data.nat.basic
namespace Nat

private def divRecLemma {x y : Nat} : 0 < y ∧ y ≤ x → x - y < x :=
λ h, and.rec (λ ypos ylex, subLt (Nat.ltOfLtOfLe ypos ylex) ypos) h

private def div.F (x : Nat) (f : Π x₁, x₁ < x → Nat → Nat) (y : Nat) : Nat :=
if h : 0 < y ∧ y ≤ x then f (x - y) (divRecLemma h) y + 1 else zero

@[extern cpp "lean::nat_div"]
protected def div (a b : @& Nat) : Nat :=
WellFounded.fix ltWf div.F a b

instance : HasDiv Nat :=
⟨Nat.div⟩

private lemma divDefAux (x y : Nat) : x / y = if h : 0 < y ∧ y ≤ x then (x - y) / y + 1 else 0 :=
congrFun (WellFounded.fixEq ltWf div.F x) y

lemma divDef (x y : Nat) : x / y = if 0 < y ∧ y ≤ x then (x - y) / y + 1 else 0 :=
difEqIf (0 < y ∧ y ≤ x) ((x - y) / y + 1) 0 ▸ divDefAux x y

private lemma {u} div.induction.F
        (C : Nat → Nat → Sort u)
        (h₁ : ∀ x y, 0 < y ∧ y ≤ x → C (x - y) y → C x y)
        (h₂ : ∀ x y, ¬(0 < y ∧ y ≤ x) → C x y)
        (x : Nat) (f : ∀ (x₁ : Nat), x₁ < x → ∀ (y : Nat), C x₁ y) (y : Nat) : C x y :=
if h : 0 < y ∧ y ≤ x then h₁ x y h (f (x - y) (divRecLemma h) y) else h₂ x y h

@[elabAsEliminator]
lemma {u} div.inductionOn
      {C : Nat → Nat → Sort u}
      (x y : Nat)
      (h₁ : ∀ x y, 0 < y ∧ y ≤ x → C (x - y) y → C x y)
      (h₂ : ∀ x y, ¬(0 < y ∧ y ≤ x) → C x y)
      : C x y :=
WellFounded.fix Nat.ltWf (div.induction.F C h₁ h₂) x y

private def mod.F (x : Nat) (f : Π x₁, x₁ < x → Nat → Nat) (y : Nat) : Nat :=
if h : 0 < y ∧ y ≤ x then f (x - y) (divRecLemma h) y else x

@[extern cpp "lean::nat_mod"]
protected def mod (a b : @& Nat) : Nat :=
WellFounded.fix ltWf mod.F a b

instance : HasMod Nat :=
⟨Nat.mod⟩

private lemma modDefAux (x y : Nat) : x % y = if h : 0 < y ∧ y ≤ x then (x - y) % y else x :=
congrFun (WellFounded.fixEq ltWf mod.F x) y

lemma modDef (x y : Nat) : x % y = if 0 < y ∧ y ≤ x then (x - y) % y else x :=
difEqIf (0 < y ∧ y ≤ x) ((x - y) % y) x ▸ modDefAux x y

@[elabAsEliminator]
lemma {u} mod.inductionOn
      {C : Nat → Nat → Sort u}
      (x y : Nat)
      (h₁ : ∀ x y, 0 < y ∧ y ≤ x → C (x - y) y → C x y)
      (h₂ : ∀ x y, ¬(0 < y ∧ y ≤ x) → C x y)
      : C x y :=
div.inductionOn x y h₁ h₂

lemma modZero (a : Nat) : a % 0 = a :=
suffices (if 0 < 0 ∧ 0 ≤ a then (a - 0) % 0 else a) = a, from (modDef a 0).symm ▸ this,
have h : ¬ (0 < 0 ∧ 0 ≤ a), from λ ⟨h₁, _⟩, absurd h₁ (Nat.ltIrrefl _),
ifNeg h

lemma modEqOfLt {a b : Nat} (h : a < b) : a % b = a :=
suffices (if 0 < b ∧ b ≤ a then (a - b) % b else a) = a, from (modDef a b).symm ▸ this,
have h' : ¬(0 < b ∧ b ≤ a), from λ ⟨_, h₁⟩, absurd h₁ (Nat.notLeOfGt h),
ifNeg h'

lemma modEqSubMod {a b : Nat} (h : a ≥ b) : a % b = (a - b) % b :=
or.elim (eqZeroOrPos b)
  (λ h₁, h₁.symm ▸ (Nat.subZero a).symm ▸ rfl)
  (λ h₁, (modDef a b).symm ▸ ifPos ⟨h₁, h⟩)

lemma modLt (x : Nat) {y : Nat} : y > 0 → x % y < y :=
mod.inductionOn x y
  (λ x y ⟨_, h₁⟩ h₂ h₃,
   have ih  : (x - y) % y < y, from h₂ h₃,
   have Heq : x % y = (x - y) % y, from modEqSubMod h₁,
   Heq.symm ▸ ih)
  (λ x y h₁ h₂,
    have h₁ : ¬ 0 < y ∨ ¬ y ≤ x, from Iff.mp (Decidable.notAndIffOrNot _ _) h₁,
    or.elim h₁
     (λ h₁, absurd h₂ h₁)
     (λ h₁,
        have hgt : y > x, from gtOfNotLe h₁,
        have Heq : x % y = x, from modEqOfLt hgt,
        Heq.symm ▸ hgt))

theorem modLe (x y : ℕ) : x % y ≤ x :=
or.elim (Nat.ltOrGe x y)
  (λ h₁ : x < y, (modEqOfLt h₁).symm ▸ Nat.leRefl _)
  (λ h₁ : x ≥ y, or.elim (eqZeroOrPos y)
    (λ h₂ : y = 0, h₂.symm ▸ (Nat.modZero x).symm ▸ Nat.leRefl _)
    (λ h₂ : y > 0, Nat.leTrans (Nat.leOfLt (Nat.modLt _ h₂)) h₁))

end Nat
