/-
Copyright (c) 2025 Lean FRO, LLC. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

prelude
import Init.Data.Int.Order

namespace Lean.Grind

class NatModule (M : Type u) extends Zero M, Add M, HSMul Nat M M where
  add_zero : ∀ a : M, a + 0 = a
  zero_add : ∀ a : M, 0 + a = a
  add_comm : ∀ a b : M, a + b = b + a
  add_assoc : ∀ a b c : M, a + b + c = a + (b + c)
  zero_smul : ∀ a : M, 0 • a = 0
  one_smul : ∀ a : M, 1 • a = a
  add_smul : ∀ n m : Nat, ∀ a : M, (n + m) • a = n • a + m • a
  smul_zero : ∀ n : Nat, n • (0 : M) = 0
  smul_add : ∀ n : Nat, ∀ a b : M, n • (a + b) = n • a + n • b
  mul_smul : ∀ n m : Nat, ∀ a : M, (n * m) • a = n • (m • a)

class IntModule (M : Type u) extends Zero M, Add M, Neg M, Sub M, HSMul Int M M where
  add_zero : ∀ a : M, a + 0 = a
  zero_add : ∀ a : M, 0 + a = a
  add_comm : ∀ a b : M, a + b = b + a
  add_assoc : ∀ a b c : M, a + b + c = a + (b + c)
  zero_smul : ∀ a : M, (0 : Int) • a = 0
  one_smul : ∀ a : M, (1 : Int) • a = a
  add_smul : ∀ n m : Int, ∀ a : M, (n + m) • a = n • a + m • a
  neg_smul : ∀ n : Int, ∀ a : M, (-n) • a = - (n • a)
  smul_zero : ∀ n : Int, n • (0 : M) = 0
  smul_add : ∀ n : Int, ∀ a b : M, n • (a + b) = n • a + n • b
  mul_smul : ∀ n m : Int, ∀ a : M, (n * m) • a = n • (m • a)
  neg_add_cancel : ∀ a : M, -a + a = 0
  sub_eq_add_neg : ∀ a b : M, a - b = a + -b

instance IntModule.toNatModule (M : Type u) [i : IntModule M] : NatModule M :=
  { i with
    hSMul a x := (a : Int) • x
    smul_zero := by simp [IntModule.smul_zero]
    add_smul := by simp [IntModule.add_smul]
    smul_add := by simp [IntModule.smul_add]
    mul_smul := by simp [IntModule.mul_smul] }

/--
We keep track of rational linear combinations as integer linear combinations,
but with the assurance that we can cancel the GCD of the coefficients.
-/
class RatModule (M : Type u) extends IntModule M where
  no_int_zero_divisors : ∀ (k : Int) (a : M), k ≠ 0 → k • a = 0 → a = 0

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
  smul_pos : ∀ (k : Int) (a : M), 0 < a → (0 < k ↔ 0 < k • a)
  smul_neg : ∀ (k : Int) (a : M), a < 0 → (0 < k ↔ k • a < 0)
  smul_nonneg : ∀ (k : Int) (a : M), 0 ≤ a → 0 ≤ k → 0 ≤ k • a
  smul_nonpos : ∀ (k : Int) (a : M), a ≤ 0 → 0 ≤ k → k • a ≤ 0

end Lean.Grind
