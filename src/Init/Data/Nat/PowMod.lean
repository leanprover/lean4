/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Copyright (c) 2022 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Bhavik Mehta
-/
module

prelude
public import Init.Data.Nat.Lemmas
import Init.Data.Bool
import Init.Omega

public section

namespace Nat

/-- Kernel reduction loop for `powMod`, with an accumulator and decreasing fuel.
The explicit recursors keep the recursive function unapplied until a branch is selected.
Adapted from Bhavik Mehta's `powModK` in PrimeCert (Apache 2.0). -/
@[expose] noncomputable def powMod.go (m : Nat) : Nat → Nat → Nat → Nat → Nat :=
  Nat.rec (fun _ _ _ => 0)
    (fun _ rec b e acc =>
      (e.beq 0).rec
        (((e.mod 2).beq 0).rec
          (rec ((b.mul b).mod m) (e.div 2) ((b.mul acc).mod m))
          (rec ((b.mul b).mod m) (e.div 2) acc))
        (acc.mod m))

/--
Computes `b ^ e % m` by square-and-multiply, reducing modulo `m` at each step so
that no intermediate value exceeds the square of the larger of `b` and `m`.

Because `Nat.mod` satisfies `n % 0 = n`, `powMod b e 0` is `b ^ e`. That case is
the exception to the bound above: there the intermediates are as large as the
result.

`powMod` is not definitionally equal to `b ^ e % m`. Concrete exponents reduce in
`O(log e)` steps under `decide`, which `b ^ e % m` could not, and `simp` evaluates
closed terms with the `Nat.reducePowMod` simproc. For symbolic reasoning, rewrite
with `powMod_def`, which is deliberately not `@[simp]`: it would turn a cheap
`powMod` goal into an intractable `b ^ e % m` one.

Examples:
* `powMod 3 4 5 = 1`
* `powMod 2 10 1000 = 24`
* `powMod 3 4 0 = 81`
-/
@[expose, extern "lean_nat_powmod"]
def powMod (b e m : @& Nat) : Nat := powMod.go m e.succ (b.mod m) e 1

private theorem powMod.go_eq (m fuel b e acc : Nat) (h : e < fuel) :
    powMod.go m fuel b e acc = (b ^ e * acc) % m := by
  induction fuel generalizing b e acc with
  | zero => omega
  | succ fuel ih =>
    change (e.beq 0).rec
      (((e % 2).beq 0).rec
        (powMod.go m fuel (b * b % m) (e / 2) (b * acc % m))
        (powMod.go m fuel (b * b % m) (e / 2) acc))
      (acc % m) = (b ^ e * acc) % m
    simp only [Bool.rec_eq, beq_eq]
    split
    next he => simp [he]
    next he =>
      split
      next hev =>
        rw [ih _ _ _ (by omega)]
        have hev' : 2 * (e / 2) = e := by omega
        rw [Nat.mul_mod, ← Nat.pow_mod, ← Nat.pow_two, ← Nat.pow_mul, hev', ← Nat.mul_mod]
      next hod =>
        rw [ih _ _ _ (by omega)]
        have hod' : 2 * (e / 2) + 1 = e := by omega
        rw [Nat.mul_mod, Nat.mod_mod, ← Nat.pow_mod, ← Nat.pow_two, ← Nat.pow_mul,
          ← Nat.mul_mod, ← Nat.mul_assoc, ← Nat.pow_succ, Nat.succ_eq_add_one, hod']

theorem powMod_def (b e m : Nat) : powMod b e m = b ^ e % m := by
  change powMod.go m (e + 1) (b % m) e 1 = _
  rw [powMod.go_eq _ _ _ _ _ (by omega), Nat.mul_one, ← Nat.pow_mod]

theorem powMod_zero (b m : Nat) : powMod b 0 m = 1 % m := by simp [powMod_def]

/-- Not `@[simp]`: it would expand a numeric exponent into repeated multiplication. -/
theorem powMod_succ (b e m : Nat) : powMod b (e + 1) m = (powMod b e m * b) % m := by
  simp [powMod_def, Nat.pow_succ, Nat.mul_mod, Nat.mod_mod]

end Nat
