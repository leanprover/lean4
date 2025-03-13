/-
Copyright (c) 2023 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
prelude
import Init.Data.Int.DivMod.Lemmas
import Init.Data.Int.Gcd

/-!
## Cooper resolution: small solutions to boundedness and divisibility constraints.
-/

namespace Int

def add_of_le {a b : Int} (h : a ≤ b) : { c : Nat // b = a + c } :=
  ⟨(b - a).toNat, by rw [Int.toNat_of_nonneg (Int.sub_nonneg_of_le h), ← Int.add_sub_assoc,
    Int.add_comm, Int.add_sub_cancel]⟩

theorem dvd_of_mul_dvd {a b c : Int} (w : a * b ∣ a * c) (h : 0 < a) : b ∣ c := by
  obtain ⟨z, w⟩ := w
  refine ⟨z, ?_⟩
  replace w := congrArg (· / a) w
  dsimp at w
  rwa [Int.mul_ediv_cancel_left _ (Int.ne_of_gt h), Int.mul_assoc,
    Int.mul_ediv_cancel_left _ (Int.ne_of_gt h)] at w

/--
Given a solution `x` to a divisibility constraint `a ∣ b * x + c`,
then `x % d` is another solution as long as `(a / gcd a b) | d`.

See `dvd_emod_add_of_dvd_add` for the specialization with `b = 1`.
-/
theorem dvd_mul_emod_add_of_dvd_mul_add {a b c d x : Int}
    (w : a ∣ b * x + c) (h : (a / gcd a b) ∣ d) :
    a ∣ b * (x % d) + c := by
  obtain ⟨p, w⟩ := w
  obtain ⟨q, rfl⟩ := h
  rw [Int.emod_def, Int.mul_sub, Int.sub_eq_add_neg, Int.add_right_comm, w,
    Int.dvd_add_right (Int.dvd_mul_right _ _), ← Int.mul_assoc, ← Int.mul_assoc, Int.dvd_neg,
    ← Int.mul_ediv_assoc b gcd_dvd_left, Int.mul_comm b a, Int.mul_ediv_assoc a gcd_dvd_right,
    Int.mul_assoc, Int.mul_assoc]
  apply Int.dvd_mul_right

/--
Given a solution `x` to a divisibility constraint `a ∣ x + c`,
then `x % d` is another solution as long as `a | d`.

See `dvd_mul_emod_add_of_dvd_mul_add` for a more general version allowing a coefficient with `x`.
-/
theorem dvd_emod_add_of_dvd_add {a c d x : Int} (w : a ∣ x + c) (h : a ∣ d) : a ∣ (x % d) + c := by
  rw [← Int.one_mul x] at w
  rw [← Int.one_mul (x % d)]
  apply dvd_mul_emod_add_of_dvd_mul_add w (by simpa)

/-!
There is an integer solution for `x` to the system
```
p ≤ a * x
    b * x ≤ q
d | c * x + s
```
(here `a`, `b`, `d` are positive integers, `c` and `s` are integers,
and `p` and `q` are integers which it may be helpful to think of as evaluations of linear forms),
if and only if there is an integer solution for `k` to the system
```
0 ≤ k < lcm a (a * d / gcd (a * d) c)
b * k + b * p ≤ a * q
    a | k + p
a * d | c * k + c * p + a * s
```
Note in the new system that `k` has explicit lower and upper bounds
(i.e. without a coefficient for `k`, and in terms of `a`, `c`, and `d` only).

This is a statement of "Cooper resolution" with a divisibility constraint,
as formulated in
"Cutting to the Chase: Solving Linear Integer Arithmetic" by Dejan Jovanović and Leonardo de Moura,
DOI 10.1007/s10817-013-9281-x

See `cooper_resolution_left` for a simpler version without the divisibility constraint.

This formulation is "biased" towards the lower bound, so it is called "left Cooper resolution".
See `cooper_resolution_dvd_right` for the version biased towards the upper bound.
-/

namespace Cooper

def resolve_left (a c d p x : Int) : Int := (a * x - p) % (lcm a (a * d / gcd (a * d) c))

/-- When `p ≤ a * x`, we can realize `resolve_left` as a natural number. -/
def resolve_left' (a c d p x : Int) (h₁ : p ≤ a * x) : Nat := (add_of_le h₁).1 % (lcm a (a * d / gcd (a * d) c))

@[simp] theorem resolve_left_eq (a c d p x : Int) (h₁ : p ≤ a * x) :
    resolve_left a c d p x = resolve_left' a c d p x h₁ := by
  simp only [resolve_left, resolve_left', add_of_le, ofNat_emod, ofNat_toNat]
  rw [Int.max_eq_left]
  omega

/-- `resolve_left` is nonnegative when `p ≤ a * x`. -/
theorem le_zero_resolve_left (a c d p x : Int) (h₁ : p ≤ a * x) :
    0 ≤ resolve_left a c d p x := by
  simp [h₁]

/-- `resolve_left` is bounded above by `lcm a (a * d / gcd (a * d) c)`. -/
theorem resolve_left_lt_lcm (a c d p x : Int) (a_pos : 0 < a) (d_pos : 0 < d) (h₁ : p ≤ a * x) :
    resolve_left a c d p x < lcm a (a * d / gcd (a * d) c) := by
  simp only [h₁, resolve_left_eq, resolve_left', add_of_le, Int.ofNat_lt]
  exact Nat.mod_lt _ (Nat.pos_of_ne_zero (lcm_ne_zero (Int.ne_of_gt a_pos)
    (Int.ne_of_gt (Int.ediv_pos_of_pos_of_dvd (Int.mul_pos a_pos d_pos) (Int.ofNat_nonneg _)
      gcd_dvd_left))))

theorem resolve_left_ineq (a c d p x : Int) (a_pos : 0 < a) (b_pos : 0 < b)
    (h₁ : p ≤ a * x) (h₂ : b * x ≤ q) :
    b * resolve_left a c d p x + b * p ≤ a * q := by
  simp only [h₁, resolve_left_eq, resolve_left']
  obtain ⟨k', w⟩ := add_of_le h₁
  replace h₂ : a * b * x ≤ a * q :=
    Int.mul_assoc _ _ _ ▸ Int.mul_le_mul_of_nonneg_left h₂ (Int.le_of_lt a_pos)
  rw [Int.mul_right_comm, w, Int.add_mul, Int.mul_comm p b, Int.mul_comm _ b] at h₂
  rw [Int.add_comm]
  calc
    _ ≤ _ := Int.add_le_add_left (Int.mul_le_mul_of_nonneg_left
                (Int.ofNat_le.mpr <| Nat.mod_le _ _) (Int.le_of_lt b_pos)) _
    _ ≤ _ := h₂

theorem resolve_left_dvd₁ (a c d p x : Int) (h₁ : p ≤ a * x) :
    a ∣ resolve_left a c d p x + p := by
  simp only [h₁, resolve_left_eq, resolve_left']
  obtain ⟨k', w⟩ := add_of_le h₁
  exact Int.ofNat_emod _ _ ▸ dvd_emod_add_of_dvd_add (x := k') ⟨x, by rw [w, Int.add_comm]⟩ dvd_lcm_left

theorem resolve_left_dvd₂ (a c d p x : Int)
    (h₁ : p ≤ a * x) (h₃ : d ∣ c * x + s) :
    a * d ∣ c * resolve_left a c d p x + c * p + a * s := by
  simp only [h₁, resolve_left_eq, resolve_left']
  obtain ⟨k', w⟩ := add_of_le h₁
  simp only [Int.add_assoc, ofNat_emod]
  apply dvd_mul_emod_add_of_dvd_mul_add
  · obtain ⟨z, r⟩ := h₃
    refine ⟨z, ?_⟩
    rw [Int.mul_assoc, ← r, Int.mul_add, Int.mul_comm c x, ← Int.mul_assoc, w, Int.add_mul,
      Int.mul_comm c, Int.mul_comm c, ← Int.add_assoc, Int.add_comm (p * c)]
  · exact Int.dvd_lcm_right

def resolve_left_inv (a p k : Int) : Int := (k + p) / a

theorem le_mul_resolve_left_inv (a p k : Int)
    (h₁ : 0 ≤ k) (h₄ : a ∣ k + p) :
    p ≤ a * resolve_left_inv a p k := by
  simp only [resolve_left_inv]
  rw [Int.mul_ediv_cancel' h₄]
  apply Int.le_add_of_nonneg_left h₁

theorem mul_resolve_left_inv_le (a p k : Int) (a_pos : 0 < a)
    (h₃ : b * k + b * p ≤ a * q) (h₄ : a ∣ k + p) :
    b * resolve_left_inv a p k ≤ q := by
  suffices h : a * (b * ((k + p) / a)) ≤ a * q from le_of_mul_le_mul_left h a_pos
  rw [Int.mul_left_comm a b, Int.mul_ediv_cancel' h₄, Int.mul_add]
  exact h₃

theorem resolve_left_inv_dvd (a c d p k : Int) (a_pos : 0 < a)
    (h₄ : a ∣ k + p) (h₅ : a * d ∣ c * k + c * p + a * s) :
    d ∣ c * resolve_left_inv a p k + s := by
  suffices h : a * d ∣ a * ((c * ((k + p) / a)) + s) from dvd_of_mul_dvd h a_pos
  rw [Int.mul_add, Int.mul_left_comm, Int.mul_ediv_cancel' h₄, Int.mul_add]
  exact h₅

end Cooper

open Cooper

/--
Left Cooper resolution of an upper and lower bound with divisibility constraint.
-/
theorem cooper_resolution_dvd_left
    {a b c d s p q : Int} (a_pos : 0 < a) (b_pos : 0 < b) (d_pos : 0 < d) :
    (∃ x, p ≤ a * x ∧ b * x ≤ q ∧ d ∣ c * x + s) ↔
    (∃ k : Int, 0 ≤ k ∧ k < lcm a (a * d / gcd (a * d) c) ∧
      b * k + b * p ≤ a * q ∧
      a ∣ k + p ∧
      a * d ∣ c * k + c * p + a * s) := by
  constructor
  · rintro ⟨x, h₁, h₂, h₃⟩
    exact ⟨resolve_left a c d p x,
      le_zero_resolve_left a c d p x h₁,
      resolve_left_lt_lcm a c d p x a_pos d_pos h₁,
      resolve_left_ineq a c d p x a_pos b_pos h₁ h₂,
      resolve_left_dvd₁ a c d p x h₁,
      resolve_left_dvd₂ a c d p x h₁ h₃⟩
  · rintro ⟨k, h₁, h₂, h₃, h₄, h₅⟩
    exact ⟨resolve_left_inv a p k,
      le_mul_resolve_left_inv a p k h₁ h₄,
      mul_resolve_left_inv_le a p k a_pos h₃ h₄,
      resolve_left_inv_dvd a c d p k a_pos h₄ h₅⟩

/--
Right Cooper resolution of an upper and lower bound with divisibility constraint.
-/
theorem cooper_resolution_dvd_right
    {a b c d s p q : Int} (a_pos : 0 < a) (b_pos : 0 < b) (d_pos : 0 < d) :
    (∃ x, p ≤ a * x ∧ b * x ≤ q ∧ d ∣ c * x + s) ↔
    (∃ k : Int, 0 ≤ k ∧ k < lcm b (b * d / gcd (b * d) c) ∧
      a * k + b * p ≤ a * q ∧
      b ∣ k - q ∧
      b * d ∣ (- c) * k + c * q + b * s) := by
  have this : ∀ x y z : Int, x + -y ≤ -z ↔ x + z ≤ y := by omega
  suffices h :
    (∃ x, p ≤ a * x ∧ b * x ≤ q ∧ d ∣ c * x + s) ↔
    (∃ k : Int, 0 ≤ k ∧ k < lcm b (b * d / gcd (b * d) (-c)) ∧
      a * k + a * (-q) ≤ b * (-p) ∧
      b ∣ k + (-q) ∧
      b * d ∣ (- c) * k + (-c) * (-q) + b * s) by
    simp only [gcd_neg, Int.neg_mul_neg] at h
    simp only [Int.mul_neg, this] at h
    exact h
  constructor
  · rintro ⟨x, lower, upper, dvd⟩
    have h : (∃ x, -q ≤ b * x ∧ a * x ≤ -p ∧ d ∣ -c * x + s) :=
      ⟨-x, Int.mul_neg _ _ ▸ Int.neg_le_neg upper, Int.mul_neg _ _ ▸ Int.neg_le_neg lower,
        by rwa [Int.neg_mul_neg _ _]⟩
    replace h := (cooper_resolution_dvd_left b_pos a_pos d_pos).mp h
    exact h
  · intro h
    obtain ⟨x, lower, upper, dvd⟩ := (cooper_resolution_dvd_left b_pos a_pos d_pos).mpr h
    refine ⟨-x, ?_, ?_, ?_⟩
    · exact Int.mul_neg _ _ ▸ Int.le_neg_of_le_neg upper
    · exact Int.mul_neg _ _ ▸ Int.neg_le_of_neg_le lower
    · exact Int.mul_neg _ _ ▸ Int.neg_mul _ _ ▸ dvd

end Int
