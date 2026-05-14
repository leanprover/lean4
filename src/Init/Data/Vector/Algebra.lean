/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

prelude
public import Init.Grind
public import Init.Data.Vector.Basic
import Init.Data.Vector.Lemmas

/-!
# Componentwise algebraic structures on `Vector α n`.
-/

public section

namespace Vector

/-- The zero vector. -/
def zero [Zero α] : Vector α n := Vector.replicate n 0

instance instZero [Zero α] : Zero (Vector α n) := ⟨zero⟩

theorem replicate_zero_eq_zero [Zero α] :
    Vector.replicate n (0 : α) = 0 :=
  (rfl)

@[simp, grind =]
theorem getElemV_zero [Zero α] {i : Nat} (h : i < n) :
    (0 : Vector α n)｢i｣ = 0 := by
  simp [← replicate_zero_eq_zero, getElemV_replicate, h]

theorem getElem_zero [Zero α] (i : Nat) (h : i < n) : (0 : Vector α n)[i] = 0 := by
  simpa using getElemV_zero h

/-- Componentwise addition of vectors. -/
def add [Add α] (xs ys : Vector α n) : Vector α n :=
  xs.zipWith (· + ·) ys

instance [Add α] : Add (Vector α n) := ⟨add⟩

theorem add_eq_zipWith [Add α] {xs ys : Vector α n} :
    xs + ys = xs.zipWith (· + ·) ys := by
  rfl

@[simp, grind =]
theorem getElemV_add [Add α] (xs ys : Vector α n) (i : Nat) (h : i < n) :
    (xs + ys)｢i｣ = xs｢i｣ + ys｢i｣ := by
  simp [add_eq_zipWith, getElemV_zipWith h]

theorem getElem_add [Add α] (xs ys : Vector α n) (i : Nat) (h : i < n) : (xs + ys)[i] = xs[i] + ys[i] := by
  simpa using getElemV_add xs ys i h

theorem add_zero [Zero α] [Add α] (add_zero : ∀ x : α, x + 0 = x) (xs : Vector α n) : xs + 0 = xs := by grind
theorem zero_add [Zero α] [Add α] (zero_add : ∀ x : α, 0 + x = x) (xs : Vector α n) : 0 + xs = xs := by grind
theorem add_comm [Add α] (add_comm : ∀ x y : α, x + y = y + x) (xs ys : Vector α n) : xs + ys = ys + xs := by grind
theorem add_assoc [Add α] (add_assoc : ∀ x y z : α, (x + y) + z = x + (y + z)) (xs ys zs : Vector α n) : (xs + ys) + zs = xs + (ys + zs) := by grind

/-- Componentwise negation of vectors. -/
def neg [Neg α] (xs : Vector α n) : Vector α n :=
  xs.map (-·)

instance [Neg α] : Neg (Vector α n) := ⟨neg⟩

theorem neg_eq_map [Neg α] {xs : Vector α n} :
    -xs = xs.map (-·) :=
  (rfl)

@[simp, grind =]
theorem getElemV_neg [Neg α] (xs : Vector α n) (i : Nat) (h : i < n) :
    (-xs)｢i｣ = -xs｢i｣ := by
  simp [neg_eq_map, getElemV_map, h]

theorem getElem_neg [Neg α] (xs : Vector α n) (i : Nat) (h : i < n) : (-xs)[i] = -xs[i] := by
  simpa using getElemV_neg xs i h

theorem neg_zero [Zero α] [Neg α] (neg_zero : -(0 : α) = 0) : -(0 : Vector α n) = 0 := by grind
theorem neg_add_cancel [Zero α] [Add α] [Neg α] (neg_add_cancel : ∀ x : α, -x + x = 0) (xs : Vector α n) : -xs + xs = 0 := by grind

/-- Componentwise subtraction of vectors. -/
def sub [Sub α] (xs ys : Vector α n) : Vector α n :=
  xs.zipWith (· - ·) ys

instance [Sub α] : Sub (Vector α n) := ⟨sub⟩

theorem sub_eq_zipWith [Sub α] {xs ys : Vector α n} :
    xs - ys = xs.zipWith (· - ·) ys :=
  (rfl)

@[simp, grind =]
theorem getElemV_sub [Sub α] (xs ys : Vector α n) (i : Nat) (h : i < n) :
    (xs - ys)｢i｣ = xs｢i｣ - ys｢i｣ := by
  simp [sub_eq_zipWith, getElemV_zipWith, h]

theorem getElem_sub [Sub α] (xs ys : Vector α n) (i : Nat) (h : i < n) : (xs - ys)[i] = xs[i] - ys[i] := by
  simpa using getElemV_sub xs ys i h

theorem sub_eq_add_neg [Sub α] [Add α] [Neg α] (sub_eq_add_neg : ∀ x y : α, x - y = x + -y) (xs ys : Vector α n) : xs - ys = xs + -ys := by grind

/-- Componentwise multiplication of vectors. -/
def mul [Mul α] (xs ys : Vector α n) : Vector α n :=
  xs.zipWith (· * ·) ys

/--
Pointwise multiplication of vectors.
This is not a global instance as in some applications different multiplications may be relevant.
-/
@[implicit_reducible]
def instMul [Mul α] : Mul (Vector α n) := ⟨mul⟩

section mul

attribute [local instance] instMul

theorem mul_eq_zipWith [Mul α] {xs ys : Vector α n} :
    xs * ys = xs.zipWith (· * ·) ys :=
  (rfl)

@[simp, grind =]
theorem getElemV_mul [Mul α] (xs ys : Vector α n) (i : Nat) (h : i < n) :
    (xs * ys)｢i｣ = xs｢i｣ * ys｢i｣ := by
  simp [mul_eq_zipWith, getElemV_zipWith, h]

theorem getElem_mul [Mul α] (xs ys : Vector α n) (i : Nat) (h : i < n) : (xs * ys)[i] = xs[i] * ys[i] := by
  simpa using getElemV_mul xs ys i h

theorem mul_zero [Zero α] [Mul α] (mul_zero : ∀ x : α, x * 0 = 0) (xs : Vector α n) : xs * 0 = 0 := by grind
theorem zero_mul [Zero α] [Mul α] (zero_mul : ∀ x : α, 0 * x = 0) (xs : Vector α n) : 0 * xs = 0 := by grind
theorem mul_comm [Mul α] (mul_comm : ∀ x y : α, x * y = y * x) (xs ys : Vector α n) : xs * ys = ys * xs := by grind
theorem mul_assoc [Mul α] (mul_assoc : ∀ x y z : α, x * (y * z) = (x * y) * z) (xs ys zs : Vector α n) : (xs * ys) * zs = xs * (ys * zs) := by grind
theorem left_distrib [Add α] [Mul α] (left_distrib : ∀ x y z : α, x * (y + z) = x * y + x * z) (xs ys zs : Vector α n) : xs * (ys + zs) = xs * ys + xs * zs := by grind
theorem right_distrib [Add α] [Mul α] (right_distrib : ∀ x y z : α, (x + y) * z = x * z + y * z) (xs ys zs : Vector α n) : (xs + ys) * zs = xs * zs + ys * zs := by grind

end mul

/-- Heterogeneous componentwise scalar multiplication of vectors. -/
def hmul [HMul α β γ] (c : α) (xs : Vector β n) : Vector γ n :=
  xs.map (c * ·)

instance [HMul α β γ] : HMul α (Vector β n) (Vector γ n) := ⟨hmul⟩

theorem hmul_eq_map [HMul α β γ] {c : α} {xs : Vector β n} :
    c * xs = xs.map (c * ·) :=
  (rfl)

@[simp, grind =]
theorem getElemV_hmul [HMul α β γ] (c : α) (xs : Vector β n) (i : Nat) (h : i < n) :
    (c * xs)｢i｣ = c * xs｢i｣ := by
  simp [hmul_eq_map, getElemV_map, h]

theorem getElem_hmul [HMul α β γ] (c : α) (xs : Vector β n) (i : Nat) (h : i < n) : (c * xs)[i] = c * xs[i] := by
  simpa using getElemV_hmul c xs i h

theorem hmul_zero [Zero β] [Zero γ] [HMul α β γ] (hmul_zero : ∀ c : α, c * (0 : β) = 0) (c : α) : c * (0 : Vector β n) = 0 := by grind
theorem zero_hmul [Zero α] [Zero β] [Zero γ] [HMul α β γ] (zero_hmul : ∀ c : β, (0 : α) * c = 0) (c : Vector β n) : (0 : α) * c = 0 := by grind
theorem hmul_add [Add β] [Add γ] [HMul α β γ] (hmul_add : ∀ c : α, ∀ x y : β, c * (x + y) = c * x + c * y) (c : α) (xs ys : Vector β n) : c * (xs + ys) = c * xs + c * ys := by grind
theorem add_hmul [Add α] [Add β] [Add γ] [HMul α β γ] (add_hmul : ∀ c d : α, ∀ x : β, (c + d) * x = c * x + d * x) (c d : α) (xs : Vector β n) : (c + d) * xs = c * xs + d * xs := by grind

/-- Componentwise scalar multiplication of vectors. -/
def smul [SMul α β] (c : α) (xs : Vector β n) : Vector β n :=
  xs.map (c • ·)

instance [SMul α β] : SMul α (Vector β n) := ⟨smul⟩

theorem smul_eq_map [SMul α β] {c : α} {xs : Vector β n} :
    c • xs = xs.map (c • ·) :=
  (rfl)

@[simp, grind =]
theorem getElemV_smul [SMul α β] (c : α) (xs : Vector β n) (i : Nat) (h : i < n) :
    (c • xs)｢i｣ = c • xs｢i｣ := by
  simp [smul_eq_map, getElemV_map, h]

theorem getElem_smul [SMul α β] (c : α) (xs : Vector β n) (i : Nat) (h : i < n) : (c • xs)[i] = c • xs[i] := by
  simpa using getElemV_smul c xs i h

theorem smul_zero [Zero β] [SMul α β] (smul_zero : ∀ c : α, c • (0 : β) = 0) (c : α) : c • (0 : Vector β n) = 0 := by grind
theorem zero_smul [Zero α] [Zero β] [SMul α β] (zero_smul : ∀ c : β, (0 : α) • c = 0) (c : Vector β n) : (0 : α) • c = 0 := by grind
theorem smul_add [Add β] [SMul α β] (smul_add : ∀ c : α, ∀ x y : β, c • (x + y) = c • x + c • y) (c : α) (xs ys : Vector β n) : c • (xs + ys) = c • xs + c • ys := by grind
theorem add_smul [Add α] [Add β] [SMul α β] (add_smul : ∀ c d : α, ∀ x : β, (c + d) • x = c • x + d • x) (c d : α) (xs : Vector β n) : (c + d) • xs = c • xs + d • xs := by grind
theorem mul_smul [Mul α] [SMul α β] (mul_smul : ∀ c d : α, ∀ x : β, (c * d) • x = c • (d • x)) (c : α) (xs : Vector β n) : (c * d) • xs = c • (d • xs) := by grind

section grind_instances

open Lean.Grind

instance [Add α] [AddRightCancel α] : AddRightCancel (Vector α n) where
  add_right_cancel x y z w := by
    ext i h
    replace w := congrArg (·｢i｣) w
    simp [h] at w
    exact AddRightCancel.add_right_cancel x｢i｣ y｢i｣ z｢i｣ w

instance [AddCommMonoid α] : AddCommMonoid (Vector α n) where
  add_zero x := add_zero AddCommMonoid.add_zero x
  add_comm x y := add_comm AddCommMonoid.add_comm x y
  add_assoc x y z := add_assoc AddCommMonoid.add_assoc x y z

instance [AddCommGroup α] : AddCommGroup (Vector α n) where
  neg_add_cancel x := neg_add_cancel AddCommGroup.neg_add_cancel x
  sub_eq_add_neg x y := sub_eq_add_neg AddCommGroup.sub_eq_add_neg x y

instance [NatModule α] : NatModule (Vector α n) where
  zero_nsmul x := zero_smul NatModule.zero_nsmul x
  add_one_nsmul x xs := by
    ext i h
    simpa [NatModule.one_nsmul, h] using congrArg (·｢i｣) (add_smul NatModule.add_nsmul x 1 xs)

instance [IntModule α] : IntModule (Vector α n) where
  zero_zsmul x := zero_smul IntModule.zero_zsmul x
  one_zsmul x := by
    ext i h
    simp [IntModule.one_zsmul, h]
  add_zsmul x xs ys := by
    ext i h
    simpa using congrArg (·｢i｣) (add_smul IntModule.add_zsmul x xs ys)
  zsmul_natCast_eq_nsmul n xs := by
    ext i h
    simp [IntModule.zsmul_natCast_eq_nsmul, h]

instance [NatModule α] [NoNatZeroDivisors α] : NoNatZeroDivisors (Vector α n) where
  no_nat_zero_divisors k a b w h := by
    ext i h'
    exact no_nat_zero_divisors k a｢i｣ b｢i｣ w (by simpa [h'] using congrArg (·｢i｣) h)

end grind_instances

end Vector

end
