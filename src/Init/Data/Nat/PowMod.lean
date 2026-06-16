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
Modular exponentiation: `powMod b e m` computes `b ^ e % m`, but overridden at
runtime to use an efficient implementation (GMP's `mpz_powm`) which performs
modular reduction at each step of repeated squaring. This avoids materializing
the (potentially enormous) intermediate value `b ^ e`.

Because `Nat.mod` satisfies `n % 0 = n`, we also have `powMod b e 0 = b ^ e`.

The logical model is square-and-multiply, halving `e` at each step and reducing
modulo `m` so that no intermediate exceeds `m * m`. It is defined by well-founded
recursion via `WellFounded.Nat.fix`, which reduces in the kernel, so `powMod`
evaluates in `O(log e)` steps under `decide` and `rfl`. The naive model
`b ^ e % m` cannot: it would materialize the (astronomically large) `b ^ e`.

The `@[semireducible]` attribute keeps the definition unfoldable by `decide` and
`rfl`; without it, well-founded definitions are marked `@[irreducible]`, which
blocks reduction at default transparency before the kernel is ever reached.
-/
@[expose, semireducible, extern "lean_nat_powmod"]
def powMod (b e m : @& Nat) : Nat :=
  if e = 0 then 1 % m
  else
    let r := powMod (b * b % m) (e / 2) m
    if e % 2 = 1 then r * b % m else r
termination_by e
decreasing_by omega

/--
`powMod` agrees with the naive `b ^ e % m`. Marked `@[simp]` so that symbolic
reasoning unfolds to the naive form (with its full lemma library); concrete
evaluation by `decide` instead reduces the efficient definition and is unaffected
by this lemma.
-/
@[simp] theorem powMod_def (b e m : Nat) : powMod b e m = b ^ e % m := by
  fun_induction powMod b e m with
  | case1 b => rw [Nat.pow_zero]
  | case2 b e hne r hodd ih =>
    show powMod (b * b % m) (e / 2) m * b % m = b ^ e % m
    have hod : 2 * (e / 2) + 1 = e := by omega
    rw [ih, ← Nat.pow_mod, ← Nat.pow_two, ← Nat.pow_mul, Nat.mod_mul_mod,
      ← Nat.pow_succ, Nat.succ_eq_add_one, hod]
  | case3 b e hne r heven ih =>
    show powMod (b * b % m) (e / 2) m = b ^ e % m
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
