/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.wf init.data.nat.basic
namespace nat

private def div_rec_lemma {x y : nat} : 0 < y ∧ y ≤ x → x - y < x :=
λ h, and.rec (λ ypos ylex, sub_lt (nat.lt_of_lt_of_le ypos ylex) ypos) h

private def div.F (x : nat) (f : Π x₁, x₁ < x → nat → nat) (y : nat) : nat :=
if h : 0 < y ∧ y ≤ x then f (x - y) (div_rec_lemma h) y + 1 else zero

@[extern cpp "lean::nat_div"]
protected def div (a b : @& nat) : nat :=
well_founded.fix lt_wf div.F a b

instance : has_div nat :=
⟨nat.div⟩

private lemma div_def_aux (x y : nat) : x / y = if h : 0 < y ∧ y ≤ x then (x - y) / y + 1 else 0 :=
congr_fun (well_founded.fix_eq lt_wf div.F x) y

lemma div_def (x y : nat) : x / y = if 0 < y ∧ y ≤ x then (x - y) / y + 1 else 0 :=
dif_eq_if (0 < y ∧ y ≤ x) ((x - y) / y + 1) 0 ▸ div_def_aux x y

private lemma {u} div.induction.F
        (C : nat → nat → Sort u)
        (h₁ : ∀ x y, 0 < y ∧ y ≤ x → C (x - y) y → C x y)
        (h₂ : ∀ x y, ¬(0 < y ∧ y ≤ x) → C x y)
        (x : nat) (f : ∀ (x₁ : nat), x₁ < x → ∀ (y : nat), C x₁ y) (y : nat) : C x y :=
if h : 0 < y ∧ y ≤ x then h₁ x y h (f (x - y) (div_rec_lemma h) y) else h₂ x y h

@[elab_as_eliminator]
lemma {u} div.induction_on
      {C : nat → nat → Sort u}
      (x y : nat)
      (h₁ : ∀ x y, 0 < y ∧ y ≤ x → C (x - y) y → C x y)
      (h₂ : ∀ x y, ¬(0 < y ∧ y ≤ x) → C x y)
      : C x y :=
well_founded.fix nat.lt_wf (div.induction.F C h₁ h₂) x y

private def mod.F (x : nat) (f : Π x₁, x₁ < x → nat → nat) (y : nat) : nat :=
if h : 0 < y ∧ y ≤ x then f (x - y) (div_rec_lemma h) y else x

@[extern cpp "lean::nat_mod"]
protected def mod (a b : @& nat) : nat :=
well_founded.fix lt_wf mod.F a b

instance : has_mod nat :=
⟨nat.mod⟩

private lemma mod_def_aux (x y : nat) : x % y = if h : 0 < y ∧ y ≤ x then (x - y) % y else x :=
congr_fun (well_founded.fix_eq lt_wf mod.F x) y

lemma mod_def (x y : nat) : x % y = if 0 < y ∧ y ≤ x then (x - y) % y else x :=
dif_eq_if (0 < y ∧ y ≤ x) ((x - y) % y) x ▸ mod_def_aux x y

@[elab_as_eliminator]
lemma {u} mod.induction_on
      {C : nat → nat → Sort u}
      (x y : nat)
      (h₁ : ∀ x y, 0 < y ∧ y ≤ x → C (x - y) y → C x y)
      (h₂ : ∀ x y, ¬(0 < y ∧ y ≤ x) → C x y)
      : C x y :=
div.induction_on x y h₁ h₂

lemma mod_zero (a : nat) : a % 0 = a :=
suffices (if 0 < 0 ∧ 0 ≤ a then (a - 0) % 0 else a) = a, from (mod_def a 0).symm ▸ this,
have h : ¬ (0 < 0 ∧ 0 ≤ a), from λ ⟨h₁, _⟩, absurd h₁ (nat.lt_irrefl _),
if_neg h

lemma mod_eq_of_lt {a b : nat} (h : a < b) : a % b = a :=
suffices (if 0 < b ∧ b ≤ a then (a - b) % b else a) = a, from (mod_def a b).symm ▸ this,
have h' : ¬(0 < b ∧ b ≤ a), from λ ⟨_, h₁⟩, absurd h₁ (nat.not_le_of_gt h),
if_neg h'

lemma mod_eq_sub_mod {a b : nat} (h : a ≥ b) : a % b = (a - b) % b :=
or.elim (eq_zero_or_pos b)
  (λ h₁, h₁.symm ▸ (nat.sub_zero a).symm ▸ rfl)
  (λ h₁, (mod_def a b).symm ▸ if_pos ⟨h₁, h⟩)

lemma mod_lt (x : nat) {y : nat} : y > 0 → x % y < y :=
mod.induction_on x y
  (λ x y ⟨_, h₁⟩ h₂ h₃,
   have ih  : (x - y) % y < y, from h₂ h₃,
   have heq : x % y = (x - y) % y, from mod_eq_sub_mod h₁,
   heq.symm ▸ ih)
  (λ x y h₁ h₂,
    have h₁ : ¬ 0 < y ∨ ¬ y ≤ x, from iff.mp (decidable.not_and_iff_or_not _ _) h₁,
    or.elim h₁
     (λ h₁, absurd h₂ h₁)
     (λ h₁,
        have hgt : y > x, from gt_of_not_le h₁,
        have heq : x % y = x, from mod_eq_of_lt hgt,
        heq.symm ▸ hgt))

theorem mod_le (x y : ℕ) : x % y ≤ x :=
or.elim (nat.lt_or_ge x y)
  (λ h₁ : x < y, (mod_eq_of_lt h₁).symm ▸ nat.le_refl _)
  (λ h₁ : x ≥ y, or.elim (eq_zero_or_pos y)
    (λ h₂ : y = 0, h₂.symm ▸ (nat.mod_zero x).symm ▸ nat.le_refl _)
    (λ h₂ : y > 0, nat.le_trans (nat.le_of_lt (nat.mod_lt _ h₂)) h₁))

end nat
