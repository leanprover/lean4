/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.WF
import Init.Data.Nat.Basic
namespace Nat

private def div_rec_lemma {x y : Nat} : 0 < y ∧ y ≤ x → x - y < x :=
  fun ⟨ypos, ylex⟩ => subLt (Nat.ltOfLtOfLe ypos ylex) ypos

private def div.F (x : Nat) (f : ∀ x₁, x₁ < x → Nat → Nat) (y : Nat) : Nat :=
  if h : 0 < y ∧ y ≤ x then f (x - y) (div_rec_lemma h) y + 1 else zero

@[extern "lean_nat_div"]
protected def div (a b : @& Nat) : Nat :=
  WellFounded.fix ltWf div.F a b

instance : Div Nat := ⟨Nat.div⟩

private theorem div_eq_aux (x y : Nat) : x / y = if h : 0 < y ∧ y ≤ x then (x - y) / y + 1 else 0 :=
  congrFun (WellFounded.fixEq ltWf div.F x) y

theorem div_eq (x y : Nat) : x / y = if 0 < y ∧ y ≤ x then (x - y) / y + 1 else 0 :=
  difEqIf (0 < y ∧ y ≤ x) ((x - y) / y + 1) 0 ▸ div_eq_aux x y

private theorem div.induction.F.{u}
        (C : Nat → Nat → Sort u)
        (ind  : ∀ x y, 0 < y ∧ y ≤ x → C (x - y) y → C x y)
        (base : ∀ x y, ¬(0 < y ∧ y ≤ x) → C x y)
        (x : Nat) (f : ∀ (x₁ : Nat), x₁ < x → ∀ (y : Nat), C x₁ y) (y : Nat) : C x y :=
  if h : 0 < y ∧ y ≤ x then ind x y h (f (x - y) (div_rec_lemma h) y) else base x y h

theorem div.inductionOn.{u}
      {motive : Nat → Nat → Sort u}
      (x y : Nat)
      (ind  : ∀ x y, 0 < y ∧ y ≤ x → motive (x - y) y → motive x y)
      (base : ∀ x y, ¬(0 < y ∧ y ≤ x) → motive x y)
      : motive x y :=
  WellFounded.fix Nat.ltWf (div.induction.F motive ind base) x y

private def mod.F (x : Nat) (f : ∀ x₁, x₁ < x → Nat → Nat) (y : Nat) : Nat :=
  if h : 0 < y ∧ y ≤ x then f (x - y) (div_rec_lemma h) y else x

@[extern "lean_nat_mod"]
protected def mod (a b : @& Nat) : Nat :=
  WellFounded.fix ltWf mod.F a b

instance : Mod Nat := ⟨Nat.mod⟩

private theorem mod_eq_aux (x y : Nat) : x % y = if h : 0 < y ∧ y ≤ x then (x - y) % y else x :=
  congrFun (WellFounded.fixEq ltWf mod.F x) y

theorem mod_eq (x y : Nat) : x % y = if 0 < y ∧ y ≤ x then (x - y) % y else x :=
  difEqIf (0 < y ∧ y ≤ x) ((x - y) % y) x ▸ mod_eq_aux x y

theorem mod.inductionOn.{u}
      {motive : Nat → Nat → Sort u}
      (x y  : Nat)
      (ind  : ∀ x y, 0 < y ∧ y ≤ x → motive (x - y) y → motive x y)
      (base : ∀ x y, ¬(0 < y ∧ y ≤ x) → motive x y)
      : motive x y :=
  div.inductionOn x y ind base

theorem mod_zero (a : Nat) : a % 0 = a :=
  have : (if 0 < 0 ∧ 0 ≤ a then (a - 0) % 0 else a) = a :=
    have h : ¬ (0 < 0 ∧ 0 ≤ a) := fun ⟨h₁, _⟩ => absurd h₁ (Nat.ltIrrefl _)
    ifNeg h
  (mod_eq a 0).symm ▸ this

theorem mod_eq_of_lt {a b : Nat} (h : a < b) : a % b = a :=
  have : (if 0 < b ∧ b ≤ a then (a - b) % b else a) = a :=
    have h' : ¬(0 < b ∧ b ≤ a) := fun ⟨_, h₁⟩ => absurd h₁ (Nat.notLeOfGt h)
    ifNeg h'
  (mod_eq a b).symm ▸ this

theorem mod_eq_sub_mod {a b : Nat} (h : a ≥ b) : a % b = (a - b) % b :=
  match eqZeroOrPos b with
  | Or.inl h₁ => h₁.symm ▸ (Nat.sub_zero a).symm ▸ rfl
  | Or.inr h₁ => (mod_eq a b).symm ▸ ifPos ⟨h₁, h⟩

theorem mod_lt (x : Nat) {y : Nat} : y > 0 → x % y < y := by
  induction x, y using mod.inductionOn with
  | base x y h₁ =>
    intro h₂
    have h₁ : ¬ 0 < y ∨ ¬ y ≤ x := Iff.mp (Decidable.notAndIffOrNot _ _) h₁
    match h₁ with
    | Or.inl h₁ => exact absurd h₂ h₁
    | Or.inr h₁ =>
      have hgt : y > x := gtOfNotLe h₁
      have heq : x % y = x := mod_eq_of_lt hgt
      rw [← heq] at hgt
      exact hgt
  | ind x y h h₂ =>
    intro h₃
    have ⟨_, h₁⟩ := h
    rw [mod_eq_sub_mod h₁]
    exact h₂ h₃

theorem mod_le (x y : Nat) : x % y ≤ x := by
  match Nat.ltOrGe x y with
  | Or.inl h₁ => rw [mod_eq_of_lt h₁]; apply Nat.leRefl
  | Or.inr h₁ => match eqZeroOrPos y with
    | Or.inl h₂ => rw [h₂, Nat.mod_zero x]; apply Nat.leRefl
    | Or.inr h₂ => exact Nat.leTrans (Nat.leOfLt (mod_lt _ h₂)) h₁

@[simp] theorem zero_mod (b : Nat) : 0 % b = 0 := by
  rw [mod_eq]
  have : ¬ (0 < b ∧ b ≤ 0) := by
    intro ⟨h₁, h₂⟩
    exact absurd (Nat.ltOfLtOfLe h₁ h₂) (Nat.ltIrrefl 0)
  simp [this]

@[simp] theorem mod_self (n : Nat) : n % n = 0 := by
  rw [mod_eq_sub_mod (Nat.leRefl _), Nat.sub_self, zero_mod]

theorem mod_one (x : Nat) : x % 1 = 0 := by
  have h : x % 1 < 1 := mod_lt x (by decide)
  have : (y : Nat) → y < 1 → y = 0 := by
    intro y
    cases y with
    | zero   => intro h; rfl
    | succ y => intro h; apply absurd (Nat.lt_of_succ_lt_succ h) (Nat.notLtZero y)
  exact this _ h

end Nat
