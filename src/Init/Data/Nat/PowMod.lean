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

public section

namespace Nat

/--
Repeated-squaring worker for `Nat.powMod`. `powModAux fuel b e m` computes
`b ^ e % m` provided `e < 2 ^ fuel`, reducing modulo `m` at each squaring step so
that no intermediate exceeds `m * m`.

The recursion is *structural* in `fuel` (so it reduces in the kernel, unlike a
well-founded definition), while `e` is halved each step, so `powMod` — taking
`fuel := e` — evaluates in `O(log e)` steps under `decide`. The current model
`b ^ e % m` cannot: it would materialize the (astronomically large) `b ^ e`.
-/
@[expose]
def powModAux (fuel b e m : Nat) : Nat :=
  match fuel with
  | 0 => 1 % m
  | fuel + 1 =>
    if e = 0 then 1 % m
    else
      let r := powModAux fuel (b * b % m) (e / 2) m
      if e % 2 = 1 then r * b % m else r

/--
Modular exponentiation: `powMod b e m` computes `b ^ e % m`, but overridden at
runtime to use an efficient implementation (GMP's `mpz_powm`) which performs
modular reduction at each step of repeated squaring. This avoids materializing
the (potentially enormous) intermediate value `b ^ e`.

Because `Nat.mod` satisfies `n % 0 = n`, we also have `powMod b e 0 = b ^ e`.

The logical model uses the kernel-reducible `powModAux` (see `powMod_def`), so
`powMod` is also efficient to evaluate by `decide`.
-/
@[expose, extern "lean_nat_powmod"]
def powMod (b e m : @& Nat) : Nat := powModAux e b e m

theorem powModAux_eq (fuel b e m : Nat) (h : e < 2 ^ fuel) :
    powModAux fuel b e m = b ^ e % m := by
  induction fuel generalizing b e with
  | zero =>
    simp only [Nat.pow_zero] at h
    have : e = 0 := by omega
    subst this; rfl
  | succ fuel ih =>
    rw [powModAux]
    split
    · next he => subst he; rfl
    · next he =>
      have he2 : e / 2 < 2 ^ fuel := by rw [Nat.pow_succ] at h; omega
      have hdm := Nat.div_add_mod e 2
      rw [ih (b * b % m) (e / 2) he2, ← Nat.pow_mod, ← Nat.pow_two, ← Nat.pow_mul]
      rcases Nat.mod_two_eq_zero_or_one e with h2 | h2
      · have hev : 2 * (e / 2) = e := by rw [h2, Nat.add_zero] at hdm; exact hdm
        rw [h2, if_neg (by decide), hev]
      · have hod : 2 * (e / 2) + 1 = e := by rw [h2] at hdm; exact hdm
        rw [h2, if_pos rfl, Nat.mod_mul_mod, ← Nat.pow_succ, Nat.succ_eq_add_one, hod]

theorem powMod_def (b e m : Nat) : powMod b e m = b ^ e % m :=
  powModAux_eq e b e m Nat.lt_two_pow_self

@[simp] theorem powMod_zero (b m : Nat) : powMod b 0 m = 1 % m := by
  simp [powMod_def]

@[simp] theorem powMod_one (b m : Nat) : powMod b 1 m = b % m := by
  simp [powMod_def]

theorem powMod_succ (b e m : Nat) : powMod b (e + 1) m = (powMod b e m * b) % m := by
  simp [powMod_def, Nat.pow_succ, Nat.mul_mod, Nat.mod_mod]

@[simp] theorem powMod_mod (b e m : Nat) : powMod b e m % m = powMod b e m := by
  simp [powMod_def, Nat.mod_mod]

theorem powMod_zero_right (b e : Nat) : powMod b e 0 = b ^ e := by
  simp [powMod_def]

end Nat
