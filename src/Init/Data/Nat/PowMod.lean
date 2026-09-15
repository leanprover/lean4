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
`go m fuel b e acc` computes `(b ^ e * acc) % m` when `e < fuel`.
`Nat.rec` avoids well-founded recursion, and `Bool.rec` avoids `Decidable` unfolding.
Adapted from Bhavik Mehta's `powModK` in PrimeCert (Apache 2.0). -/
@[expose] noncomputable def powMod.go (m : Nat) : Nat → Nat → Nat → Nat → Nat :=
  Nat.rec (fun _ _ _ => 0)
    (fun _ rec b e acc =>
      (e.beq 0).rec
        (((e.mod 2).beq 0).rec
          (rec ((b.mul b).mod m) (e.div 2) ((b.mul acc).mod m))
          (rec ((b.mul b).mod m) (e.div 2) acc))
        (acc.mod m))

/-- Fixed-window loop: `window b m k fuel e` computes `b ^ e % m` when
`2 ≤ k` and `e < fuel`. The small powers use the kernel's `Nat.pow` reduction. -/
@[expose] noncomputable def powMod.window (b m k : Nat) : Nat → Nat → Nat :=
  Nat.rec (fun _ => 0)
    (fun _ rec e =>
      (e.beq 0).rec
        ((((rec (e.div k)).pow k).mul (b.pow (e.mod k))).mod m)
        ((1 : Nat).mod m))

private theorem powMod.window_eq (b m k fuel e : Nat) (hk : 2 ≤ k) (h : e < fuel) :
    powMod.window b m k fuel e = b ^ e % m := by
  induction fuel generalizing e with
  | zero => omega
  | succ fuel ih =>
    change (e.beq 0).rec
      (((powMod.window b m k fuel (e / k)) ^ k * b ^ (e % k)) % m)
      (1 % m) = b ^ e % m
    simp only [Bool.rec_eq, beq_eq]
    split
    next he => simp [he]
    next he =>
      have hdiv : e / k < fuel := Nat.lt_of_lt_of_le
        (Nat.div_lt_self (Nat.pos_of_ne_zero he) (by omega)) (by omega)
      rw [ih _ hdiv, Nat.mul_mod, ← Nat.pow_mod, ← Nat.pow_mul,
        ← Nat.mul_mod, ← Nat.pow_add, Nat.div_add_mod']

/--
Computes `b ^ e % m` using modular exponentiation.

The Lean definition uses four-bit windows for `m ≤ 2 ^ 512`, three-bit windows for
`m ≤ 2 ^ 1024`, and square-and-multiply for larger moduli. Windows trade larger
intermediate integers for fewer kernel reductions: for positive `m`, intermediates
are bounded by `m ^ 31`, `m ^ 15`, and `m ^ 2`, respectively. Compiled execution
uses GMP modular exponentiation.

Because `Nat.mod` satisfies `n % 0 = n`, `powMod b e 0` is `b ^ e`; in that case
intermediates can be as large as the result.

`powMod` is not definitionally equal to `b ^ e % m`. Concrete exponents reduce in
`O(log e)` steps under `decide`, which `b ^ e % m` could not, and `simp` evaluates
closed terms with the `Nat.reducePowMod` simproc. For symbolic reasoning, rewrite
with `powMod_def`; unfolding can stop at the window selection for a symbolic modulus.
This theorem is deliberately not `@[simp]`: it would turn a cheap
`powMod` goal into an intractable `b ^ e % m` one.

Examples:
* `powMod 3 4 5 = 1`
* `powMod 2 10 1000 = 24`
* `powMod 3 4 0 = 81`
-/
@[expose, extern "lean_nat_powmod"]
def powMod (b e m : @& Nat) : Nat :=
  -- Shifts keep the bounds reducible under Meta's default exponentiation limit.
  (e.beq 0).rec
    ((m.ble ((1 : Nat).shiftLeft 1024)).rec
      (powMod.go m e.succ (b.mod m) e 1)
      ((m.ble ((1 : Nat).shiftLeft 512)).rec
        (powMod.window (b.mod m) m 8 e.succ e)
        (powMod.window (b.mod m) m 16 e.succ e)))
    ((1 : Nat).mod m)

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
  simp only [powMod, Bool.rec_eq, beq_eq]
  split
  next he => subst e; rfl
  next he =>
    split
    next =>
      split
      all_goals
        rw [powMod.window_eq _ _ _ _ _ (by decide) (by omega)]
        exact (Nat.pow_mod b e m).symm
    next =>
      rw [powMod.go_eq _ _ _ _ _ (by omega), Nat.mul_one]
      exact (Nat.pow_mod b e m).symm

theorem powMod_zero (b m : Nat) : powMod b 0 m = 1 % m := by simp [powMod_def]

/-- Not `@[simp]`: it would expand a numeric exponent into repeated multiplication. -/
theorem powMod_succ (b e m : Nat) : powMod b (e + 1) m = (powMod b e m * b) % m := by
  simp [powMod_def, Nat.pow_succ, Nat.mul_mod, Nat.mod_mod]

end Nat
