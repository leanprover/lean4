/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.wf init.data.nat.basic
namespace nat

private def divRecLemma {x y : nat} : 0 < y ∧ y ≤ x → x - y < x :=
λ h, and.rec (λ ypos ylex, subLt (nat.ltOfLtOfLe ypos ylex) ypos) h

private def div.F (x : nat) (f : Π x₁, x₁ < x → nat → nat) (y : nat) : nat :=
if h : 0 < y ∧ y ≤ x then f (x - y) (divRecLemma h) y + 1 else zero

@[extern cpp "lean::natDiv"]
protected def div (a b : @& nat) : nat :=
wellFounded.fix ltWf div.F a b

instance : hasDiv nat :=
⟨nat.div⟩

private lemma divDefAux (x y : nat) : x / y = if h : 0 < y ∧ y ≤ x then (x - y) / y + 1 else 0 :=
congrFun (wellFounded.fixEq ltWf div.F x) y

lemma divDef (x y : nat) : x / y = if 0 < y ∧ y ≤ x then (x - y) / y + 1 else 0 :=
difEqIf (0 < y ∧ y ≤ x) ((x - y) / y + 1) 0 ▸ divDefAux x y

private lemma {u} div.induction.F
        (C : nat → nat → Sort u)
        (h₁ : ∀ x y, 0 < y ∧ y ≤ x → C (x - y) y → C x y)
        (h₂ : ∀ x y, ¬(0 < y ∧ y ≤ x) → C x y)
        (x : nat) (f : ∀ (x₁ : nat), x₁ < x → ∀ (y : nat), C x₁ y) (y : nat) : C x y :=
if h : 0 < y ∧ y ≤ x then h₁ x y h (f (x - y) (divRecLemma h) y) else h₂ x y h

@[elabAsEliminator]
lemma {u} div.inductionOn
      {C : nat → nat → Sort u}
      (x y : nat)
      (h₁ : ∀ x y, 0 < y ∧ y ≤ x → C (x - y) y → C x y)
      (h₂ : ∀ x y, ¬(0 < y ∧ y ≤ x) → C x y)
      : C x y :=
wellFounded.fix nat.ltWf (div.induction.F C h₁ h₂) x y

private def mod.F (x : nat) (f : Π x₁, x₁ < x → nat → nat) (y : nat) : nat :=
if h : 0 < y ∧ y ≤ x then f (x - y) (divRecLemma h) y else x

@[extern cpp "lean::natMod"]
protected def mod (a b : @& nat) : nat :=
wellFounded.fix ltWf mod.F a b

instance : hasMod nat :=
⟨nat.mod⟩

private lemma modDefAux (x y : nat) : x % y = if h : 0 < y ∧ y ≤ x then (x - y) % y else x :=
congrFun (wellFounded.fixEq ltWf mod.F x) y

lemma modDef (x y : nat) : x % y = if 0 < y ∧ y ≤ x then (x - y) % y else x :=
difEqIf (0 < y ∧ y ≤ x) ((x - y) % y) x ▸ modDefAux x y

@[elabAsEliminator]
lemma {u} mod.inductionOn
      {C : nat → nat → Sort u}
      (x y : nat)
      (h₁ : ∀ x y, 0 < y ∧ y ≤ x → C (x - y) y → C x y)
      (h₂ : ∀ x y, ¬(0 < y ∧ y ≤ x) → C x y)
      : C x y :=
div.inductionOn x y h₁ h₂

lemma modZero (a : nat) : a % 0 = a :=
suffices (if 0 < 0 ∧ 0 ≤ a then (a - 0) % 0 else a) = a, from (modDef a 0).symm ▸ this,
have h : ¬ (0 < 0 ∧ 0 ≤ a), from λ ⟨h₁, _⟩, absurd h₁ (nat.ltIrrefl _),
ifNeg h

lemma modEqOfLt {a b : nat} (h : a < b) : a % b = a :=
suffices (if 0 < b ∧ b ≤ a then (a - b) % b else a) = a, from (modDef a b).symm ▸ this,
have h' : ¬(0 < b ∧ b ≤ a), from λ ⟨_, h₁⟩, absurd h₁ (nat.notLeOfGt h),
ifNeg h'

lemma modEqSubMod {a b : nat} (h : a ≥ b) : a % b = (a - b) % b :=
or.elim (eqZeroOrPos b)
  (λ h₁, h₁.symm ▸ (nat.subZero a).symm ▸ rfl)
  (λ h₁, (modDef a b).symm ▸ ifPos ⟨h₁, h⟩)

lemma modLt (x : nat) {y : nat} : y > 0 → x % y < y :=
mod.inductionOn x y
  (λ x y ⟨_, h₁⟩ h₂ h₃,
   have ih  : (x - y) % y < y, from h₂ h₃,
   have heq : x % y = (x - y) % y, from modEqSubMod h₁,
   heq.symm ▸ ih)
  (λ x y h₁ h₂,
    have h₁ : ¬ 0 < y ∨ ¬ y ≤ x, from iff.mp (decidable.notAndIffOrNot _ _) h₁,
    or.elim h₁
     (λ h₁, absurd h₂ h₁)
     (λ h₁,
        have hgt : y > x, from gtOfNotLe h₁,
        have heq : x % y = x, from modEqOfLt hgt,
        heq.symm ▸ hgt))

theorem modLe (x y : ℕ) : x % y ≤ x :=
or.elim (nat.ltOrGe x y)
  (λ h₁ : x < y, (modEqOfLt h₁).symm ▸ nat.leRefl _)
  (λ h₁ : x ≥ y, or.elim (eqZeroOrPos y)
    (λ h₂ : y = 0, h₂.symm ▸ (nat.modZero x).symm ▸ nat.leRefl _)
    (λ h₂ : y > 0, nat.leTrans (nat.leOfLt (nat.modLt _ h₂)) h₁))

end nat
