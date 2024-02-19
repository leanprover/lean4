/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.WF
import Init.WFTactics
import Init.Data.Nat.Basic

namespace Nat

theorem div_rec_lemma {x y : Nat} : 0 < y ∧ y ≤ x → x - y < x :=
  fun ⟨ypos, ylex⟩ => sub_lt (Nat.lt_of_lt_of_le ypos ylex) ypos

@[extern "lean_nat_div"]
protected def div (x y : @& Nat) : Nat :=
  if 0 < y ∧ y ≤ x then
    Nat.div (x - y) y + 1
  else
    0
decreasing_by apply div_rec_lemma; assumption

instance : Div Nat := ⟨Nat.div⟩

theorem div_eq (x y : Nat) : x / y = if 0 < y ∧ y ≤ x then (x - y) / y + 1 else 0 := by
  show Nat.div x y = _
  rw [Nat.div]
  rfl

theorem div.inductionOn.{u}
      {motive : Nat → Nat → Sort u}
      (x y : Nat)
      (ind  : ∀ x y, 0 < y ∧ y ≤ x → motive (x - y) y → motive x y)
      (base : ∀ x y, ¬(0 < y ∧ y ≤ x) → motive x y)
      : motive x y :=
  if h : 0 < y ∧ y ≤ x then
    ind x y h (inductionOn (x - y) y ind base)
  else
    base x y h
decreasing_by apply div_rec_lemma; assumption

theorem div_le_self (n k : Nat) : n / k ≤ n := by
  induction n using Nat.strongInductionOn with
  | ind n ih =>
    rw [div_eq]
    -- Note: manual split to avoid Classical.em which is not yet defined
    cases (inferInstance : Decidable (0 < k ∧ k ≤ n)) with
    | isFalse h => simp [h]
    | isTrue h =>
      suffices (n - k) / k + 1 ≤ n by simp [h, this]
      have ⟨hK, hKN⟩ := h
      have hSub : n - k < n := sub_lt (Nat.lt_of_lt_of_le hK hKN) hK
      have : (n - k) / k ≤ n - k := ih (n - k) hSub
      exact succ_le_of_lt (Nat.lt_of_le_of_lt this hSub)

theorem div_lt_self {n k : Nat} (hLtN : 0 < n) (hLtK : 1 < k) : n / k < n := by
  rw [div_eq]
  cases (inferInstance : Decidable (0 < k ∧ k ≤ n)) with
  | isFalse h => simp [hLtN, h]
  | isTrue h =>
    suffices (n - k) / k + 1 < n by simp [h, this]
    have ⟨_, hKN⟩ := h
    have : (n - k) / k ≤ n - k := div_le_self (n - k) k
    have := Nat.add_le_of_le_sub hKN this
    exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hLtK _) this

@[extern "lean_nat_mod"]
protected def modCore (x y : @& Nat) : Nat :=
  if 0 < y ∧ y ≤ x then
    Nat.modCore (x - y) y
  else
    x
decreasing_by apply div_rec_lemma; assumption

@[extern "lean_nat_mod"]
protected def mod : @& Nat → @& Nat → Nat
  /- This case is not needed mathematically as the case below is equal to it; however, it makes
  `0 % n = 0` true definitionally rather than just propositionally.
  This property is desirable for `Fin n`, as it means `(ofNat 0 : Fin n).val = 0` by definition.
  Primarily, this is valuable because mathlib in Lean3 assumed this was true definitionally, and so
  keeping this definitional equality makes mathlib easier to port to mathlib4. -/
  | 0, _ => 0
  | x@(_ + 1), y => Nat.modCore x y

instance : Mod Nat := ⟨Nat.mod⟩

protected theorem modCore_eq_mod (x y : Nat) : Nat.modCore x y = x % y := by
  cases x with
  | zero =>
    rw [Nat.modCore]
    exact if_neg fun ⟨hlt, hle⟩ => Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hlt hle)
  | succ x => rfl

theorem mod_eq (x y : Nat) : x % y = if 0 < y ∧ y ≤ x then (x - y) % y else x := by
  rw [←Nat.modCore_eq_mod, ←Nat.modCore_eq_mod, Nat.modCore]

theorem mod.inductionOn.{u}
      {motive : Nat → Nat → Sort u}
      (x y  : Nat)
      (ind  : ∀ x y, 0 < y ∧ y ≤ x → motive (x - y) y → motive x y)
      (base : ∀ x y, ¬(0 < y ∧ y ≤ x) → motive x y)
      : motive x y :=
  div.inductionOn x y ind base

@[simp] theorem mod_zero (a : Nat) : a % 0 = a :=
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
  have : ¬ (0 < b ∧ b = 0) := by
    intro ⟨h₁, h₂⟩
    simp_all
  simp [this]

@[simp] theorem mod_self (n : Nat) : n % n = 0 := by
  rw [mod_eq_sub_mod (Nat.le_refl _), Nat.sub_self, zero_mod]

theorem mod_one (x : Nat) : x % 1 = 0 := by
  have h : x % 1 < 1 := mod_lt x (by decide)
  have : (y : Nat) → y < 1 → y = 0 := by
    intro y
    cases y with
    | zero   => intro _; rfl
    | succ y => intro h; apply absurd (Nat.lt_of_succ_lt_succ h) (Nat.not_lt_zero y)
  exact this _ h

theorem div_add_mod (m n : Nat) : n * (m / n) + m % n = m := by
  rw [div_eq, mod_eq]
  have h : Decidable (0 < n ∧ n ≤ m) := inferInstance
  cases h with
  | isFalse h => simp [h]
  | isTrue h =>
    simp [h]
    have ih := div_add_mod (m - n) n
    rw [Nat.left_distrib, Nat.mul_one, Nat.add_assoc, Nat.add_left_comm, ih, Nat.add_comm, Nat.sub_add_cancel h.2]
decreasing_by apply div_rec_lemma; assumption

theorem div_eq_sub_div (h₁ : 0 < b) (h₂ : b ≤ a) : a / b = (a - b) / b + 1 := by
 rw [div_eq a, if_pos]; constructor <;> assumption


theorem mod_add_div (m k : Nat) : m % k + k * (m / k) = m := by
  induction m, k using mod.inductionOn with rw [div_eq, mod_eq]
  | base x y h => simp [h]
  | ind x y h IH => simp [h]; rw [Nat.mul_succ, ← Nat.add_assoc, IH, Nat.sub_add_cancel h.2]

@[simp] protected theorem div_one (n : Nat) : n / 1 = n := by
  have := mod_add_div n 1
  rwa [mod_one, Nat.zero_add, Nat.one_mul] at this

@[simp] protected theorem div_zero (n : Nat) : n / 0 = 0 := by
  rw [div_eq]; simp [Nat.lt_irrefl]

@[simp] protected theorem zero_div (b : Nat) : 0 / b = 0 :=
  (div_eq 0 b).trans <| if_neg <| And.rec Nat.not_le_of_gt

theorem le_div_iff_mul_le (k0 : 0 < k) : x ≤ y / k ↔ x * k ≤ y := by
  induction y, k using mod.inductionOn generalizing x with
    (rw [div_eq]; simp [h]; cases x with | zero => simp [zero_le] | succ x => ?_)
  | base y k h =>
    simp [not_succ_le_zero x, succ_mul, Nat.add_comm]
    refine Nat.lt_of_lt_of_le ?_ (Nat.le_add_right ..)
    exact Nat.not_le.1 fun h' => h ⟨k0, h'⟩
  | ind y k h IH =>
    rw [← add_one, Nat.add_le_add_iff_right, IH k0, succ_mul,
        ← Nat.add_sub_cancel (x*k) k, Nat.sub_le_sub_iff_right h.2, Nat.add_sub_cancel]

theorem div_mul_le_self : ∀ (m n : Nat), m / n * n ≤ m
  | m, 0   => by simp
  | m, n+1 => (le_div_iff_mul_le (Nat.succ_pos _)).1 (Nat.le_refl _)

theorem div_lt_iff_lt_mul (Hk : 0 < k) : x / k < y ↔ x < y * k := by
  rw [← Nat.not_le, ← Nat.not_le]; exact not_congr (le_div_iff_mul_le Hk)

@[simp] theorem add_div_right (x : Nat) {z : Nat} (H : 0 < z) : (x + z) / z = succ (x / z) := by
  rw [div_eq_sub_div H (Nat.le_add_left _ _), Nat.add_sub_cancel]

@[simp] theorem add_div_left (x : Nat) {z : Nat} (H : 0 < z) : (z + x) / z = succ (x / z) := by
  rw [Nat.add_comm, add_div_right x H]

theorem add_mul_div_left (x z : Nat) {y : Nat} (H : 0 < y) : (x + y * z) / y = x / y + z := by
  induction z with
  | zero => rw [Nat.mul_zero, Nat.add_zero, Nat.add_zero]
  | succ z ih => rw [mul_succ, ← Nat.add_assoc, add_div_right _ H, ih]; rfl

theorem add_mul_div_right (x y : Nat) {z : Nat} (H : 0 < z) : (x + y * z) / z = x / z + y := by
  rw [Nat.mul_comm, add_mul_div_left _ _ H]

@[simp] theorem add_mod_right (x z : Nat) : (x + z) % z = x % z := by
  rw [mod_eq_sub_mod (Nat.le_add_left ..), Nat.add_sub_cancel]

@[simp] theorem add_mod_left (x z : Nat) : (x + z) % x = z % x := by
  rw [Nat.add_comm, add_mod_right]

@[simp] theorem add_mul_mod_self_left (x y z : Nat) : (x + y * z) % y = x % y := by
  match z with
  | 0 => rw [Nat.mul_zero, Nat.add_zero]
  | succ z => rw [mul_succ, ← Nat.add_assoc, add_mod_right, add_mul_mod_self_left (z := z)]

@[simp] theorem add_mul_mod_self_right (x y z : Nat) : (x + y * z) % z = x % z := by
  rw [Nat.mul_comm, add_mul_mod_self_left]

@[simp] theorem mul_mod_right (m n : Nat) : (m * n) % m = 0 := by
  rw [← Nat.zero_add (m * n), add_mul_mod_self_left, zero_mod]

@[simp] theorem mul_mod_left (m n : Nat) : (m * n) % n = 0 := by
  rw [Nat.mul_comm, mul_mod_right]

protected theorem div_eq_of_lt_le (lo : k * n ≤ m) (hi : m < succ k * n) : m / n = k :=
have npos : 0 < n := (eq_zero_or_pos _).resolve_left fun hn => by
  rw [hn, Nat.mul_zero] at hi lo; exact absurd lo (Nat.not_le_of_gt hi)
Nat.le_antisymm
  (le_of_lt_succ ((Nat.div_lt_iff_lt_mul npos).2 hi))
  ((Nat.le_div_iff_mul_le npos).2 lo)

theorem sub_mul_div (x n p : Nat) (h₁ : n*p ≤ x) : (x - n*p) / n = x / n - p := by
  match eq_zero_or_pos n with
  | .inl h₀ => rw [h₀, Nat.div_zero, Nat.div_zero, Nat.zero_sub]
  | .inr h₀ => induction p with
    | zero => rw [Nat.mul_zero, Nat.sub_zero, Nat.sub_zero]
    | succ p IH =>
      have h₂ : n * p ≤ x := Nat.le_trans (Nat.mul_le_mul_left _ (le_succ _)) h₁
      have h₃ : x - n * p ≥ n := by
        apply Nat.le_of_add_le_add_right
        rw [Nat.sub_add_cancel h₂, Nat.add_comm]
        rw [mul_succ] at h₁
        exact h₁
      rw [sub_succ, ← IH h₂, div_eq_sub_div h₀ h₃]
      simp [add_one, Nat.pred_succ, mul_succ, Nat.sub_sub]

theorem mul_sub_div (x n p : Nat) (h₁ : x < n*p) : (n * p - succ x) / n = p - succ (x / n) := by
  have npos : 0 < n := (eq_zero_or_pos _).resolve_left fun n0 => by
    rw [n0, Nat.zero_mul] at h₁; exact not_lt_zero _ h₁
  apply Nat.div_eq_of_lt_le
  focus
    rw [Nat.mul_sub_right_distrib, Nat.mul_comm]
    exact Nat.sub_le_sub_left ((div_lt_iff_lt_mul npos).1 (lt_succ_self _)) _
  focus
    show succ (pred (n * p - x)) ≤ (succ (pred (p - x / n))) * n
    rw [succ_pred_eq_of_pos (Nat.sub_pos_of_lt h₁),
      fun h => succ_pred_eq_of_pos (Nat.sub_pos_of_lt h)] -- TODO: why is the function needed?
    focus
      rw [Nat.mul_sub_right_distrib, Nat.mul_comm]
      exact Nat.sub_le_sub_left (div_mul_le_self ..) _
    focus
      rwa [div_lt_iff_lt_mul npos, Nat.mul_comm]

theorem mul_mod_mul_left (z x y : Nat) : (z * x) % (z * y) = z * (x % y) :=
  if y0 : y = 0 then by
    rw [y0, Nat.mul_zero, mod_zero, mod_zero]
  else if z0 : z = 0 then by
    rw [z0, Nat.zero_mul, Nat.zero_mul, Nat.zero_mul, mod_zero]
  else by
    induction x using Nat.strongInductionOn with
    | _ n IH =>
      have y0 : y > 0 := Nat.pos_of_ne_zero y0
      have z0 : z > 0 := Nat.pos_of_ne_zero z0
      cases Nat.lt_or_ge n y with
      | inl yn => rw [mod_eq_of_lt yn, mod_eq_of_lt (Nat.mul_lt_mul_of_pos_left yn z0)]
      | inr yn =>
        rw [mod_eq_sub_mod yn, mod_eq_sub_mod (Nat.mul_le_mul_left z yn),
          ← Nat.mul_sub_left_distrib]
        exact IH _ (sub_lt (Nat.lt_of_lt_of_le y0 yn) y0)

theorem div_eq_of_lt (h₀ : a < b) : a / b = 0 := by
  rw [div_eq a, if_neg]
  intro h₁
  apply Nat.not_le_of_gt h₀ h₁.right

end Nat
