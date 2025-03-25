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

/--
Divisibility of natural numbers. `a ∣ b` (typed as `\|`) says that
there is some `c` such that `b = a * c`.
-/
instance : Dvd Nat where
  dvd a b := Exists (fun c => b = a * c)

theorem div_rec_lemma {x y : Nat} : 0 < y ∧ y ≤ x → x - y < x :=
  fun ⟨ypos, ylex⟩ => sub_lt (Nat.lt_of_lt_of_le ypos ylex) ypos

theorem div_rec_fuel_lemma {x y fuel : Nat} (hy : 0 < y) (hle : y ≤ x) (hfuel : x < fuel + 1) :
    x - y < fuel :=
  Nat.lt_of_lt_of_le (div_rec_lemma ⟨hy, hle⟩) (Nat.le_of_lt_succ hfuel)

/--
Division of natural numbers, discarding the remainder. Division by `0` returns `0`. Usually accessed
via the `/` operator.

This operation is sometimes called “floor division.”

This function is overridden at runtime with an efficient implementation. This definition is
the logical model.

Examples:
 * `21 / 3 = 7`
 * `21 / 5 = 4`
 * `0 / 22 = 0`
 * `5 / 0 = 0`
-/
@[extern "lean_nat_div", irreducible]
protected def div (x y : @& Nat) : Nat :=
  if hy : 0 < y then
    let rec
      go (fuel : Nat) (x : Nat) (hfuel : x < fuel) : Nat :=
      match fuel with
      | 0 => by contradiction
      | succ fuel =>
        if h : y ≤ x then
          go fuel (x - y) (div_rec_fuel_lemma hy h hfuel) + 1
        else
          0
      termination_by structural fuel
    go (x + 1) x (Nat.lt_succ_self _)
  else
    0

instance instDiv : Div Nat := ⟨Nat.div⟩

private theorem div.go.fuel_congr (x y fuel1 fuel2 : Nat) (hy : 0 < y) (h1 : x < fuel1) (h2 : x < fuel2) :
    Nat.div.go y hy fuel1 x h1 = Nat.div.go y hy fuel2 x h2 := by
  match fuel1, fuel2 with
  | 0, _ => contradiction
  | _, 0 => contradiction
  | succ fuel1, succ fuel2  =>
    simp only [Nat.div.go]
    split
    next => rw [Nat.div.go.fuel_congr]
    next => rfl
termination_by structural fuel1

theorem div_eq (x y : Nat) : x / y = if 0 < y ∧ y ≤ x then (x - y) / y + 1 else 0 := by
  show Nat.div _ _ = ite _ (Nat.div _ _ + 1) _
  unfold Nat.div
  split
  next =>
    rw [Nat.div.go]
    split
    next =>
      simp only [and_self, ↓reduceIte, *]
      congr 1
      apply div.go.fuel_congr
    next =>
      simp only [and_false, ↓reduceIte, *]
  next =>
    simp only [false_and, ↓reduceIte, *]

/--
An induction principle customized for reasoning about the recursion pattern of natural number
division by iterated subtraction.
-/
def div.inductionOn.{u}
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
  induction n using Nat.strongRecOn with
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

/--
The modulo operator, which computes the remainder when dividing one natural number by another.
Usually accessed via the `%` operator. When the divisor is `0`, the result is the dividend rather
than an error.

This is the core implementation of `Nat.mod`. It computes the correct result for any two closed
natural numbers, but it does not have some convenient [definitional
reductions](lean-manual://section/type-system) when the `Nat`s contain free variables. The wrapper
`Nat.mod` handles those cases specially and then calls `Nat.modCore`.

This function is overridden at runtime with an efficient implementation. This definition is the
logical model.
-/
@[extern "lean_nat_mod", irreducible]
protected noncomputable def modCore (x y : Nat) : Nat :=
  if hy : 0 < y then
    let rec
      go (fuel : Nat) (x : Nat) (hfuel : x < fuel) : Nat :=
      match fuel with
      | 0 => by contradiction
      | succ fuel =>
        if h : y ≤ x then
          go fuel (x - y) (div_rec_fuel_lemma hy h hfuel)
        else
          x
      termination_by structural fuel
    go (x + 1) x (Nat.lt_succ_self _)
  else
    x

private theorem modCore.go.fuel_congr (x y fuel1 fuel2 : Nat) (hy : 0 < y) (h1 : x < fuel1) (h2 : x < fuel2) :
    Nat.modCore.go y hy fuel1 x h1 = Nat.modCore.go y hy fuel2 x h2 := by
  match fuel1, fuel2 with
  | 0, _ => contradiction
  | _, 0 => contradiction
  | succ fuel1, succ fuel2  =>
    simp only [Nat.modCore.go]
    split
    next => rw [Nat.modCore.go.fuel_congr]
    next => rfl
termination_by structural fuel1

protected theorem modCore_eq (x y : Nat) : Nat.modCore x y =
  if 0 < y ∧ y ≤ x then
    Nat.modCore (x - y) y
  else
    x := by
  unfold Nat.modCore
  split
  next =>
    rw [Nat.modCore.go]
    split
    next =>
      simp only [and_self, ↓reduceIte, *]
      apply modCore.go.fuel_congr
    next =>
      simp only [and_false, ↓reduceIte, *]
  next =>
    simp only [false_and, ↓reduceIte, *]


/--
The modulo operator, which computes the remainder when dividing one natural number by another.
Usually accessed via the `%` operator. When the divisor is `0`, the result is the dividend rather
than an error.

`Nat.mod` is a wrapper around `Nat.modCore` that special-cases two situations, giving better
definitional reductions:
 * `Nat.mod 0 m` should reduce to `m`, for all terms `m : Nat`.
 * `Nat.mod n (m + n + 1)` should reduce to `n` for concrete `Nat` literals `n`.

These reductions help `Fin n` literals work well, because the `OfNat` instance for `Fin` uses
`Nat.mod`. In particular, `(0 : Fin (n + 1)).val` should reduce definitionally to `0`. `Nat.modCore`
can handle all numbers, but its definitional reductions are not as convenient.

This function is overridden at runtime with an efficient implementation. This definition is the
logical model.

Examples:
 * `7 % 2 = 1`
 * `9 % 3 = 0`
 * `5 % 7 = 5`
 * `5 % 0 = 5`
 * `show ∀ (n : Nat), 0 % n = 0 from fun _ => rfl`
 * `show ∀ (m : Nat), 5 % (m + 6) = 5 from fun _ => rfl`
-/
@[extern "lean_nat_mod"]
protected def mod : @& Nat → @& Nat → Nat
  /-
  Nat.modCore is defined with fuel and thus does not reduce with open terms very well.
  Nevertheless it is desirable for trivial `Nat.mod` calculations, namely
  * `Nat.mod 0 m` for all `m`
  * `Nat.mod n (m + n + 1)` for concrete literals `n`,
  to reduce definitionally.
  This property is desirable for `Fin n` literals, as it means `(ofNat 0 : Fin n).val = 0` by
  definition.
   -/
  | 0, _ => 0
  | n@(_ + 1), m =>
    if m ≤ n -- NB: if n < m does not reduce as well as `m ≤ n`!
    then Nat.modCore n m
    else n

instance instMod : Mod Nat := ⟨Nat.mod⟩

protected theorem modCore_eq_mod (n m : Nat) : Nat.modCore n m = n % m := by
  show Nat.modCore n m = Nat.mod n m
  match n, m with
  | 0, _ =>
    rw [Nat.modCore_eq]
    exact if_neg fun ⟨hlt, hle⟩ => Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hlt hle)
  | (_ + 1), _ =>
    rw [Nat.mod]; dsimp
    refine iteInduction (fun _ => rfl) (fun h => ?false) -- cannot use `split` this early yet
    rw [Nat.modCore_eq]
    exact if_neg fun ⟨_hlt, hle⟩ => h hle

theorem mod_eq (x y : Nat) : x % y = if 0 < y ∧ y ≤ x then (x - y) % y else x := by
  rw [←Nat.modCore_eq_mod, ←Nat.modCore_eq_mod, Nat.modCore_eq]

/--
An induction principle customized for reasoning about the recursion pattern of `Nat.mod`.
-/
def mod.inductionOn.{u}
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

@[simp] theorem one_mod_eq_zero_iff {n : Nat} : 1 % n = 0 ↔ n = 1 := by
  match n with
  | 0 => simp
  | 1 => simp
  | n + 2 =>
    rw [mod_eq_of_lt (by exact Nat.lt_of_sub_eq_succ rfl)]
    simp only [add_one_ne_zero, false_iff, ne_eq]
    exact ne_of_beq_eq_false rfl

@[simp] theorem zero_eq_one_mod_iff {n : Nat} : 0 = 1 % n ↔ n = 1 := by
  rw [eq_comm]
  simp

theorem mod_eq_sub_mod {a b : Nat} (h : a ≥ b) : a % b = (a - b) % b :=
  match eq_zero_or_pos b with
  | Or.inl h₁ => h₁.symm ▸ (Nat.sub_zero a).symm ▸ rfl
  | Or.inr h₁ => (mod_eq a b).symm ▸ if_pos ⟨h₁, h⟩

theorem mod_lt (x : Nat) {y : Nat} : y > 0 → x % y < y := by
  induction x, y using mod.inductionOn with
  | base x y h₁ =>
    intro h₂
    have h₁ : ¬ 0 < y ∨ ¬ y ≤ x := Decidable.not_and_iff_or_not.mp h₁
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

@[simp] protected theorem sub_mod_add_mod_cancel (a b : Nat) [NeZero a] : a - b % a + b % a = a := by
  rw [Nat.sub_add_cancel]
  cases a with
  | zero => simp_all
  | succ a =>
    exact Nat.le_of_lt (mod_lt b (zero_lt_succ a))

theorem mod_le (x y : Nat) : x % y ≤ x := by
  match Nat.lt_or_ge x y with
  | Or.inl h₁ => rw [mod_eq_of_lt h₁]; apply Nat.le_refl
  | Or.inr h₁ => match eq_zero_or_pos y with
    | Or.inl h₂ => rw [h₂, Nat.mod_zero x]; apply Nat.le_refl
    | Or.inr h₂ => exact Nat.le_trans (Nat.le_of_lt (mod_lt _ h₂)) h₁

theorem mod_lt_of_lt {a b c : Nat} (h : a < c) : a % b < c :=
  Nat.lt_of_le_of_lt (Nat.mod_le _ _) h

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

theorem mod_def (m k : Nat) : m % k = m - k * (m / k) := by
  rw [Nat.sub_eq_of_eq_add]
  apply (Nat.mod_add_div _ _).symm

theorem mod_eq_sub_mul_div {x k : Nat} : x % k = x - k * (x / k) := mod_def _ _

theorem mod_eq_sub_div_mul {x k : Nat} : x % k = x - (x / k) * k := by
  rw [mod_eq_sub_mul_div, Nat.mul_comm]

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
    simp only [add_one, succ_mul, false_iff, Nat.not_le, Nat.succ_ne_zero]
    refine Nat.lt_of_lt_of_le ?_ (Nat.le_add_left ..)
    exact Nat.not_le.1 fun h' => h ⟨k0, h'⟩
  | ind y k h IH =>
    rw [Nat.add_le_add_iff_right, IH k0, succ_mul,
        ← Nat.add_sub_cancel (x*k) k, Nat.sub_le_sub_iff_right h.2, Nat.add_sub_cancel]

protected theorem div_div_eq_div_mul (m n k : Nat) : m / n / k = m / (n * k) := by
  cases eq_zero_or_pos k with
  | inl k0 => rw [k0, Nat.mul_zero, Nat.div_zero, Nat.div_zero] | inr kpos => ?_
  cases eq_zero_or_pos n with
  | inl n0 => rw [n0, Nat.zero_mul, Nat.div_zero, Nat.zero_div] | inr npos => ?_

  apply Nat.le_antisymm

  apply (le_div_iff_mul_le (Nat.mul_pos npos kpos)).2
  rw [Nat.mul_comm n k, ← Nat.mul_assoc]
  apply (le_div_iff_mul_le npos).1
  apply (le_div_iff_mul_le kpos).1
  (apply Nat.le_refl)

  apply (le_div_iff_mul_le kpos).2
  apply (le_div_iff_mul_le npos).2
  rw [Nat.mul_assoc, Nat.mul_comm n k]
  apply (le_div_iff_mul_le (Nat.mul_pos kpos npos)).1
  apply Nat.le_refl

theorem div_mul_le_self : ∀ (m n : Nat), m / n * n ≤ m
  | m, 0   => by simp
  | _, _+1 => (le_div_iff_mul_le (Nat.succ_pos _)).1 (Nat.le_refl _)

theorem div_lt_iff_lt_mul (Hk : 0 < k) : x / k < y ↔ x < y * k := by
  rw [← Nat.not_le, ← Nat.not_le]; exact not_congr (le_div_iff_mul_le Hk)

theorem pos_of_div_pos {a b : Nat} (h : 0 < a / b) : 0 < a := by
  cases b with
  | zero => simp at h
  | succ b =>
    match a, h with
    | 0, h => simp at h
    | a + 1, _ => exact zero_lt_succ a

@[simp] theorem add_div_right (x : Nat) {z : Nat} (H : 0 < z) : (x + z) / z = (x / z) + 1 := by
  rw [div_eq_sub_div H (Nat.le_add_left _ _), Nat.add_sub_cancel]

@[simp] theorem add_div_left (x : Nat) {z : Nat} (H : 0 < z) : (z + x) / z = (x / z) + 1 := by
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

@[simp] theorem mul_add_mod_self_left (a b c : Nat) : (a * b + c) % a = c % a := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_left]

@[simp] theorem add_mul_mod_self_right (x y z : Nat) : (x + y * z) % z = x % z := by
  rw [Nat.mul_comm, add_mul_mod_self_left]

@[simp] theorem mul_add_mod_self_right (a b c : Nat) : (a * b + c) % b = c % b := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right]

@[simp] theorem mul_mod_right (m n : Nat) : (m * n) % m = 0 := by
  rw [← Nat.zero_add (m * n), add_mul_mod_self_left, zero_mod]

@[simp] theorem mul_mod_left (m n : Nat) : (m * n) % n = 0 := by
  rw [Nat.mul_comm, mul_mod_right]

protected theorem div_eq_of_lt_le (lo : k * n ≤ m) (hi : m < (k + 1) * n) : m / n = k :=
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
      simp [Nat.pred_succ, mul_succ, Nat.sub_sub]

theorem mul_sub_div (x n p : Nat) (h₁ : x < n*p) : (n * p - (x + 1)) / n = p - ((x / n) + 1) := by
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
    induction x using Nat.strongRecOn with
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

protected theorem mul_div_cancel (m : Nat) {n : Nat} (H : 0 < n) : m * n / n = m := by
  let t := add_mul_div_right 0 m H
  rwa [Nat.zero_add, Nat.zero_div, Nat.zero_add] at t

protected theorem mul_div_cancel_left (m : Nat) {n : Nat} (H : 0 < n) : n * m / n = m := by
  rw [Nat.mul_comm, Nat.mul_div_cancel _ H]

protected theorem div_le_of_le_mul {m n : Nat} : ∀ {k}, m ≤ k * n → m / k ≤ n
  | 0, _ => by simp [Nat.div_zero, n.zero_le]
  | succ k, h => by
    suffices succ k * (m / succ k) ≤ succ k * n from
      Nat.le_of_mul_le_mul_left this (zero_lt_succ _)
    have h1 : succ k * (m / succ k) ≤ m % succ k + succ k * (m / succ k) := Nat.le_add_left _ _
    have h2 : m % succ k + succ k * (m / succ k) = m := by rw [mod_add_div]
    have h3 : m ≤ succ k * n := h
    rw [← h2] at h3
    exact Nat.le_trans h1 h3

@[simp] theorem mul_div_right (n : Nat) {m : Nat} (H : 0 < m) : m * n / m = n := by
  induction n <;> simp_all [mul_succ]

@[simp] theorem mul_div_left (m : Nat) {n : Nat} (H : 0 < n) : m * n / n = m := by
  rw [Nat.mul_comm, mul_div_right _ H]

protected theorem div_self (H : 0 < n) : n / n = 1 := by
  let t := add_div_right 0 H
  rwa [Nat.zero_add, Nat.zero_div] at t

protected theorem div_eq_of_eq_mul_left (H1 : 0 < n) (H2 : m = k * n) : m / n = k :=
by rw [H2, Nat.mul_div_cancel _ H1]

protected theorem div_eq_of_eq_mul_right (H1 : 0 < n) (H2 : m = n * k) : m / n = k :=
by rw [H2, Nat.mul_div_cancel_left _ H1]

protected theorem mul_div_mul_left {m : Nat} (n k : Nat) (H : 0 < m) :
    m * n / (m * k) = n / k := by rw [← Nat.div_div_eq_div_mul, Nat.mul_div_cancel_left _ H]

protected theorem mul_div_mul_right {m : Nat} (n k : Nat) (H : 0 < m) :
    n * m / (k * m) = n / k := by rw [Nat.mul_comm, Nat.mul_comm k, Nat.mul_div_mul_left _ _ H]

theorem mul_div_le (m n : Nat) : n * (m / n) ≤ m := by
  match n, Nat.eq_zero_or_pos n with
  | _, Or.inl rfl => rw [Nat.zero_mul]; exact m.zero_le
  | n, Or.inr h => rw [Nat.mul_comm, ← Nat.le_div_iff_mul_le h]; exact Nat.le_refl _


end Nat
