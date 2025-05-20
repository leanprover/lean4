/-
Copyright (c) 2025 Lean FRO, LLC. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

prelude
import Init.Data.Int.Order

namespace Lean.Grind

class NatModule (M : Type u) extends Zero M, Add M, HMul Nat M M where
  add_zero : ∀ a : M, a + 0 = a
  zero_add : ∀ a : M, 0 + a = a
  add_comm : ∀ a b : M, a + b = b + a
  add_assoc : ∀ a b c : M, a + b + c = a + (b + c)
  zero_hmul : ∀ a : M, 0 * a = 0
  one_hmul : ∀ a : M, 1 * a = a
  add_hmul : ∀ n m : Nat, ∀ a : M, (n + m) * a = n * a + m * a
  hmul_zero : ∀ n : Nat, n * (0 : M) = 0
  hmul_add : ∀ n : Nat, ∀ a b : M, n * (a + b) = n * a + n * b
  mul_hmul : ∀ n m : Nat, ∀ a : M, (n * m) * a = n * (m * a)

attribute [instance 100] NatModule.toZero NatModule.toAdd NatModule.toHMul

class IntModule (M : Type u) extends Zero M, Add M, Neg M, Sub M, HMul Int M M where
  add_zero : ∀ a : M, a + 0 = a
  zero_add : ∀ a : M, 0 + a = a
  add_comm : ∀ a b : M, a + b = b + a
  add_assoc : ∀ a b c : M, a + b + c = a + (b + c)
  zero_hmul : ∀ a : M, (0 : Int) * a = 0
  one_hmul : ∀ a : M, (1 : Int) * a = a
  add_hmul : ∀ n m : Int, ∀ a : M, (n + m) * a = n * a + m * a
  neg_hmul : ∀ n : Int, ∀ a : M, (-n) * a = - (n * a)
  hmul_zero : ∀ n : Int, n * (0 : M) = 0
  hmul_add : ∀ n : Int, ∀ a b : M, n * (a + b) = n * a + n * b
  mul_hmul : ∀ n m : Int, ∀ a : M, (n * m) * a = n * (m * a)
  neg_add_cancel : ∀ a : M, -a + a = 0
  sub_eq_add_neg : ∀ a b : M, a - b = a + -b

attribute [instance 100] IntModule.toZero IntModule.toAdd IntModule.toNeg IntModule.toSub IntModule.toHMul

instance IntModule.toNatModule (M : Type u) [i : IntModule M] : NatModule M :=
  { i with
    hMul a x := (a : Int) * x
    hmul_zero := by simp [IntModule.hmul_zero]
    add_hmul := by simp [IntModule.add_hmul]
    hmul_add := by simp [IntModule.hmul_add]
    mul_hmul := by simp [IntModule.mul_hmul] }

/--
We keep track of rational linear combinations as integer linear combinations,
but with the assurance that we can cancel the GCD of the coefficients.
-/
class RatModule (M : Type u) extends IntModule M where
  no_int_zero_divisors : ∀ (k : Int) (a : M), k ≠ 0 → k * a = 0 → a = 0

/-- A preorder is a reflexive, transitive relation `≤` with `a < b` defined in the obvious way. -/
class Preorder (α : Type u) extends LE α, LT α where
  le_refl : ∀ a : α, a ≤ a
  le_trans : ∀ a b c : α, a ≤ b → b ≤ c → a ≤ c
  lt := fun a b => a ≤ b ∧ ¬b ≤ a
  lt_iff_le_not_le : ∀ a b : α, a < b ↔ a ≤ b ∧ ¬b ≤ a := by intros; rfl

class IntModule.IsOrdered (M : Type u) [Preorder M] [IntModule M] where
  neg_le_iff : ∀ a b : M, -a ≤ b ↔ -b ≤ a
  neg_lt_iff : ∀ a b : M, -a < b ↔ -b < a
  add_lt_left : ∀ a b c : M, a < b → a + c < b + c
  add_lt_right : ∀ a b c : M, a < b → c + a < c + b
  hmul_pos : ∀ (k : Int) (a : M), 0 < a → (0 < k ↔ 0 < k * a)
  hmul_neg : ∀ (k : Int) (a : M), a < 0 → (0 < k ↔ k * a < 0)
  hmul_nonneg : ∀ (k : Int) (a : M), 0 ≤ a → 0 ≤ k → 0 ≤ k * a
  hmul_nonpos : ∀ (k : Int) (a : M), a ≤ 0 → 0 ≤ k → k * a ≤ 0

end Lean.Grind
