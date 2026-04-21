/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

prelude
public import Init.Data.Nat.Lemmas

public section

namespace Nat

/--
Modular exponentiation: `powMod b e m` computes `b ^ e % m`, but overridden at
runtime to use an efficient implementation (GMP's `mpz_powm`) which performs
modular reduction at each step of repeated squaring. This avoids materializing
the (potentially enormous) intermediate value `b ^ e`.

Because `Nat.mod` satisfies `n % 0 = n`, we also have `powMod b e 0 = b ^ e`.

The definition provided here is the logical model.
-/
@[expose, extern "lean_nat_powmod"]
def powMod (b e m : @& Nat) : Nat := b ^ e % m

theorem powMod_def (b e m : Nat) : powMod b e m = b ^ e % m := (rfl)

@[simp] theorem powMod_zero (b m : Nat) : powMod b 0 m = 1 % m := by
  simp [powMod_def]

@[simp] theorem powMod_one (b m : Nat) : powMod b 1 m = b % m := by
  simp [powMod_def]

theorem powMod_succ (b e m : Nat) : powMod b (e + 1) m = powMod b e m * b % m := by
  simp [powMod_def, Nat.pow_succ, Nat.mul_mod, Nat.mod_mod]

@[simp] theorem powMod_mod (b e m : Nat) : powMod b e m % m = powMod b e m := by
  simp [powMod_def, Nat.mod_mod]

theorem powMod_zero_right (b e : Nat) : powMod b e 0 = b ^ e := by
  simp [powMod_def]

end Nat
