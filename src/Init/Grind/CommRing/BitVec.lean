/-
Copyright (c) 2025 Lean FRO, LLC. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
prelude
import Init.Grind.CommRing.Basic
import Init.Data.BitVec.Lemmas

namespace BitVec

-- TODO: this should be replaced via an `@[extern]` with a native implementation
def pow (x : BitVec w) (n : Nat) : BitVec w :=
  match n with
  | 0 => 1
  | n + 1 => pow x n * x

instance : HPow (BitVec w) Nat (BitVec w) where
  hPow x n := pow x n

theorem pow_zero (x : BitVec w) : x ^ 0 = 1 := rfl
theorem pow_succ (x : BitVec w) (n : Nat) : x ^ (n + 1) = x ^ n * x := rfl

end BitVec

namespace Lean.Grind

instance : CommRing (BitVec w) where
  add_assoc := BitVec.add_assoc
  add_comm := BitVec.add_comm
  add_zero := BitVec.add_zero
  neg_add_cancel := BitVec.add_left_neg
  mul_assoc := BitVec.mul_assoc
  mul_comm := BitVec.mul_comm
  mul_one := BitVec.mul_one
  left_distrib _ _ _ := BitVec.mul_add
  zero_mul _ := BitVec.zero_mul
  sub_eq_add_neg := BitVec.sub_eq_add_neg
  pow_zero := BitVec.pow_zero
  pow_succ := BitVec.pow_succ
  ofNat_add := BitVec.ofNat_add
  ofNat_mul := BitVec.ofNat_mul

instance : IsCharP (BitVec w) (2 ^ w) where
  char {x} := by
    simp [BitVec.ofInt, BitVec.toNat_eq]

end Lean.Grind
