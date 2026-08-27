/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

prelude
public import Init.Data.Nat.Lemmas
import Init.Omega
import Init.RCases
import Init.WFTactics

public section

namespace Nat

/--
Computes `b ^ e % m` without ever forming the intermediate value `b ^ e`.

Because `Nat.mod` satisfies `n % 0 = n`, `powMod b e 0` is `b ^ e`.

`powMod` is not definitionally equal to `b ^ e % m`. Its logical model is
square-and-multiply, so that concrete exponents reduce in `O(log e)` steps rather
than forming `b ^ e`; use `powMod_def` to rewrite to the naive form for symbolic
reasoning.

Examples:
* `powMod 3 4 5 = 1`
* `powMod 2 10 1000 = 24`
* `powMod 3 4 0 = 81`
-/
@[expose, semireducible, extern "lean_nat_powmod"]
def powMod (b e m : @& Nat) : Nat :=
  if e = 0 then 1 % m
  else
    let r := powMod (b * b % m) (e / 2) m
    if e % 2 = 1 then r * b % m else r
termination_by e
decreasing_by omega

@[simp] theorem powMod_def (b e m : Nat) : powMod b e m = b ^ e % m := by
  fun_induction powMod b e m with
  | case1 b => rw [Nat.pow_zero]
  | case2 b e hne r hodd ih =>
    subst r
    have hod : 2 * (e / 2) + 1 = e := by omega
    rw [ih, ← Nat.pow_mod, ← Nat.pow_two, ← Nat.pow_mul, Nat.mod_mul_mod,
      ← Nat.pow_succ, Nat.succ_eq_add_one, hod]
  | case3 b e hne r heven ih =>
    subst r
    have hev : 2 * (e / 2) = e := by omega
    rw [ih, ← Nat.pow_mod, ← Nat.pow_two, ← Nat.pow_mul, hev]

/-- `powMod b 0 m = 1 % m`. Recurrence base case; not `@[simp]` since `powMod_def`
already simplifies `powMod`. -/
theorem powMod_zero (b m : Nat) : powMod b 0 m = 1 % m := by simp

/-- `powMod b (e + 1) m = (powMod b e m * b) % m`. Recurrence step; not `@[simp]`
since `powMod_def` already simplifies `powMod`. -/
theorem powMod_succ (b e m : Nat) : powMod b (e + 1) m = (powMod b e m * b) % m := by
  simp [Nat.pow_succ, Nat.mul_mod, Nat.mod_mod]

end Nat
