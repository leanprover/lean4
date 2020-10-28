/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.WF
import Init.Data.Nat.Basic
namespace Nat

private def divRecLemma {x y : Nat} : 0 < y ∧ y ≤ x → x - y < x :=
  fun ⟨ypos, ylex⟩ => subLt (Nat.ltOfLtOfLe ypos ylex) ypos

private def div.F (x : Nat) (f : ∀ x₁, x₁ < x → Nat → Nat) (y : Nat) : Nat :=
  if h : 0 < y ∧ y ≤ x then f (x - y) (divRecLemma h) y + 1 else zero

@[extern "lean_nat_div"]
protected def div (a b : @& Nat) : Nat :=
  WellFounded.fix ltWf div.F a b

instance : Div Nat := ⟨Nat.div⟩

private theorem divDefAux (x y : Nat) : x / y = if h : 0 < y ∧ y ≤ x then (x - y) / y + 1 else 0 :=
  congrFun (WellFounded.fixEq ltWf div.F x) y

theorem divDef (x y : Nat) : x / y = if 0 < y ∧ y ≤ x then (x - y) / y + 1 else 0 :=
  difEqIf (0 < y ∧ y ≤ x) ((x - y) / y + 1) 0 ▸ divDefAux x y

private theorem div.induction.F.{u}
        (C : Nat → Nat → Sort u)
        (h₁ : ∀ x y, 0 < y ∧ y ≤ x → C (x - y) y → C x y)
        (h₂ : ∀ x y, ¬(0 < y ∧ y ≤ x) → C x y)
        (x : Nat) (f : ∀ (x₁ : Nat), x₁ < x → ∀ (y : Nat), C x₁ y) (y : Nat) : C x y :=
  if h : 0 < y ∧ y ≤ x then h₁ x y h (f (x - y) (divRecLemma h) y) else h₂ x y h

@[elabAsEliminator]
theorem div.inductionOn.{u}
      {motive : Nat → Nat → Sort u}
      (x y : Nat)
      (h₁ : ∀ x y, 0 < y ∧ y ≤ x → motive (x - y) y → motive x y)
      (h₂ : ∀ x y, ¬(0 < y ∧ y ≤ x) → motive x y)
      : motive x y :=
  WellFounded.fix Nat.ltWf (div.induction.F motive h₁ h₂) x y

private def mod.F (x : Nat) (f : ∀ x₁, x₁ < x → Nat → Nat) (y : Nat) : Nat :=
  if h : 0 < y ∧ y ≤ x then f (x - y) (divRecLemma h) y else x

@[extern "lean_nat_mod"]
protected def mod (a b : @& Nat) : Nat :=
  WellFounded.fix ltWf mod.F a b

instance : Mod Nat := ⟨Nat.mod⟩

private theorem modDefAux (x y : Nat) : x % y = if h : 0 < y ∧ y ≤ x then (x - y) % y else x :=
  congrFun (WellFounded.fixEq ltWf mod.F x) y

theorem modDef (x y : Nat) : x % y = if 0 < y ∧ y ≤ x then (x - y) % y else x :=
  difEqIf (0 < y ∧ y ≤ x) ((x - y) % y) x ▸ modDefAux x y

@[elabAsEliminator]
theorem mod.inductionOn.{u}
      {motive : Nat → Nat → Sort u}
      (x y : Nat)
      (h₁ : ∀ x y, 0 < y ∧ y ≤ x → motive (x - y) y → motive x y)
      (h₂ : ∀ x y, ¬(0 < y ∧ y ≤ x) → motive x y)
      : motive x y :=
  div.inductionOn x y h₁ h₂

theorem modZero (a : Nat) : a % 0 = a :=
  have (if 0 < 0 ∧ 0 ≤ a then (a - 0) % 0 else a) = a from
    have h : ¬ (0 < 0 ∧ 0 ≤ a) from fun ⟨h₁, _⟩ => absurd h₁ (Nat.ltIrrefl _)
    ifNeg h
  (modDef a 0).symm ▸ this

theorem modEqOfLt {a b : Nat} (h : a < b) : a % b = a :=
  have (if 0 < b ∧ b ≤ a then (a - b) % b else a) = a from
    have h' : ¬(0 < b ∧ b ≤ a) from fun ⟨_, h₁⟩ => absurd h₁ (Nat.notLeOfGt h)
    ifNeg h'
  (modDef a b).symm ▸ this

theorem modEqSubMod {a b : Nat} (h : a ≥ b) : a % b = (a - b) % b :=
  Or.elim (eqZeroOrPos b)
    (fun h₁ => h₁.symm ▸ (Nat.subZero a).symm ▸ rfl)
    (fun h₁ => (modDef a b).symm ▸ ifPos ⟨h₁, h⟩)

theorem modLt (x : Nat) {y : Nat} : y > 0 → x % y < y := by
   refine mod.inductionOn (motive := fun x y => y > 0 → x % y < y) x y ?k1 ?k2
   case k1 =>
     intro x y ⟨_, h₁⟩ h₂ h₃
     rw [modEqSubMod h₁]
     exact h₂ h₃
   case k2 =>
     intro x y h₁ h₂
     have h₁ : ¬ 0 < y ∨ ¬ y ≤ x from Iff.mp (Decidable.notAndIffOrNot _ _) h₁
     match h₁ with
     | Or.inl h₁ => exact absurd h₂ h₁
     | Or.inr h₁ =>
       have hgt : y > x from gtOfNotLe h₁
       have heq : x % y = x from modEqOfLt hgt
       rw [← heq] at hgt
       exact hgt

theorem modLe (x y : Nat) : x % y ≤ x := by
  match Nat.ltOrGe x y with
  | Or.inl h₁ => rw [modEqOfLt h₁]; apply Nat.leRefl
  | Or.inr h₁ => match eqZeroOrPos y with
    | Or.inl h₂ => rw [h₂, Nat.modZero x]; apply Nat.leRefl
    | Or.inr h₂ => exact Nat.leTrans (Nat.leOfLt (Nat.modLt _ h₂)) h₁

end Nat
