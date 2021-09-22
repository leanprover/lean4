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
  fun ⟨ypos, ylex⟩ => sub_lt (Nat.lt_of_lt_of_le ypos ylex) ypos

private def div.F (x : Nat) (f : ∀ x₁, x₁ < x → Nat → Nat) (y : Nat) : Nat :=
  if h : 0 < y ∧ y ≤ x then f (x - y) (div_rec_lemma h) y + 1 else zero

@[extern "lean_nat_div"]
protected def div (a b : @& Nat) : Nat :=
  WellFounded.fix (measure id) div.F a b

instance : Div Nat := ⟨Nat.div⟩

private theorem div_eq_aux (x y : Nat) : x / y = if h : 0 < y ∧ y ≤ x then (x - y) / y + 1 else 0 :=
  congrFun (WellFounded.fix_eq (measure id) div.F x) y

theorem div_eq (x y : Nat) : x / y = if 0 < y ∧ y ≤ x then (x - y) / y + 1 else 0 :=
  dif_eq_if (0 < y ∧ y ≤ x) ((x - y) / y + 1) 0 ▸ div_eq_aux x y

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
  WellFounded.fix (measure id) (div.induction.F motive ind base) x y

private def mod.F (x : Nat) (f : ∀ x₁, x₁ < x → Nat → Nat) (y : Nat) : Nat :=
  if h : 0 < y ∧ y ≤ x then f (x - y) (div_rec_lemma h) y else x

@[extern "lean_nat_mod"]
protected def mod (a b : @& Nat) : Nat :=
  WellFounded.fix lt_wf mod.F a b

instance : Mod Nat := ⟨Nat.mod⟩

private theorem mod_eq_aux (x y : Nat) : x % y = if h : 0 < y ∧ y ≤ x then (x - y) % y else x :=
  congrFun (WellFounded.fix_eq (measure id) mod.F x) y

theorem mod_eq (x y : Nat) : x % y = if 0 < y ∧ y ≤ x then (x - y) % y else x :=
  dif_eq_if (0 < y ∧ y ≤ x) ((x - y) % y) x ▸ mod_eq_aux x y

theorem mod.inductionOn.{u}
      {motive : Nat → Nat → Sort u}
      (x y  : Nat)
      (ind  : ∀ x y, 0 < y ∧ y ≤ x → motive (x - y) y → motive x y)
      (base : ∀ x y, ¬(0 < y ∧ y ≤ x) → motive x y)
      : motive x y :=
  div.inductionOn x y ind base

theorem mod_zero (a : Nat) : a % 0 = a :=
  have : (if 0 < 0 ∧ 0 ≤ a then (a - 0) % 0 else a) = a :=
    have h : ¬ (0 < 0 ∧ 0 ≤ a) := fun ⟨h₁, _⟩ => absurd h₁ (Nat.lt_irrefl _)
    if_neg h
  (mod_eq a 0).symm ▸ this

theorem mod_eq_of_lt {a b : Nat} (h : a < b) : a % b = a :=
  have : (if 0 < b ∧ b ≤ a then (a - b) % b else a) = a :=
    have h' : ¬(0 < b ∧ b ≤ a) := fun ⟨_, h₁⟩ => absurd h₁ (Nat.not_le_of_gt h)
    if_neg h'
  (mod_eq a b).symm ▸ this

theorem mod_eq_sub_mod {a b : Nat} (h : a ≥ b) : a % b = (a - b) % b :=
  match eq_zero_or_pos b with
  | Or.inl h₁ => h₁.symm ▸ (Nat.sub_zero a).symm ▸ rfl
  | Or.inr h₁ => (mod_eq a b).symm ▸ if_pos ⟨h₁, h⟩

theorem mod_lt (x : Nat) {y : Nat} : y > 0 → x % y < y := by
  induction x, y using mod.inductionOn with
  | base x y h₁ =>
    intro h₂
    have h₁ : ¬ 0 < y ∨ ¬ y ≤ x := Iff.mp (Decidable.not_and_iff_or_not _ _) h₁
    match h₁ with
    | Or.inl h₁ => exact absurd h₂ h₁
    | Or.inr h₁ =>
      have hgt : y > x := gt_of_not_le h₁
      have heq : x % y = x := mod_eq_of_lt hgt
      rw [← heq] at hgt
      exact hgt
  | ind x y h h₂ =>
    intro h₃
    have ⟨_, h₁⟩ := h
    rw [mod_eq_sub_mod h₁]
    exact h₂ h₃

theorem mod_le (x y : Nat) : x % y ≤ x := by
  match Nat.lt_or_ge x y with
  | Or.inl h₁ => rw [mod_eq_of_lt h₁]; apply Nat.le_refl
  | Or.inr h₁ => match eq_zero_or_pos y with
    | Or.inl h₂ => rw [h₂, Nat.mod_zero x]; apply Nat.le_refl
    | Or.inr h₂ => exact Nat.le_trans (Nat.le_of_lt (mod_lt _ h₂)) h₁

@[simp] theorem zero_mod (b : Nat) : 0 % b = 0 := by
  rw [mod_eq]
  have : ¬ (0 < b ∧ b ≤ 0) := by
    intro ⟨h₁, h₂⟩
    exact absurd (Nat.lt_of_lt_of_le h₁ h₂) (Nat.lt_irrefl 0)
  simp [this]

@[simp] theorem mod_self (n : Nat) : n % n = 0 := by
  rw [mod_eq_sub_mod (Nat.le_refl _), Nat.sub_self, zero_mod]

theorem mod_one (x : Nat) : x % 1 = 0 := by
  have h : x % 1 < 1 := mod_lt x (by decide)
  have : (y : Nat) → y < 1 → y = 0 := by
    intro y
    cases y with
    | zero   => intro h; rfl
    | succ y => intro h; apply absurd (Nat.lt_of_succ_lt_succ h) (Nat.not_lt_zero y)
  exact this _ h

end Nat
