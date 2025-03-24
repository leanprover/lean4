/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
prelude
import Init.Data.Int.Basic
import Init.Data.Nat.Gcd
import Init.Data.Nat.Lcm
import Init.Data.Int.DivMod.Lemmas

/-!
Definition and lemmas for gcd and lcm over Int

## Future work
Most of the material about `Nat.gcd` and `Nat.lcm` from `Init.Data.Nat.Gcd` and `Init.Data.Nat.Lcm`
has analogues for `Int.gcd` and `Int.lcm` that should be added to this file.
-/
namespace Int

/-! ## gcd -/

/--
Computes the greatest common divisor of two integers as a natural number. The GCD of two integers is
the largest natural number that evenly divides both. However, the GCD of a number and `0` is the
number's absolute value.

This implementation uses `Nat.gcd`, which is overridden in both the kernel and the compiler to
efficiently evaluate using arbitrary-precision arithmetic.

Examples:
* `Int.gcd 10 15 = 5`
* `Int.gcd 10 (-15) = 5`
* `Int.gcd (-6) (-9) = 3`
* `Int.gcd 0 5 = 5`
* `Int.gcd (-7) 0 = 7`
-/
def gcd (m n : Int) : Nat := m.natAbs.gcd n.natAbs

theorem gcd_dvd_left {a b : Int} : (gcd a b : Int) ∣ a := by
  have := Nat.gcd_dvd_left a.natAbs b.natAbs
  rw [← Int.ofNat_dvd] at this
  exact Int.dvd_trans this natAbs_dvd_self

theorem gcd_dvd_right {a b : Int} : (gcd a b : Int) ∣ b := by
  have := Nat.gcd_dvd_right a.natAbs b.natAbs
  rw [← Int.ofNat_dvd] at this
  exact Int.dvd_trans this natAbs_dvd_self

@[simp] theorem one_gcd {a : Int} : gcd 1 a = 1 := by simp [gcd]
@[simp] theorem gcd_one {a : Int} : gcd a 1 = 1 := by simp [gcd]

@[simp] theorem neg_gcd {a b : Int} : gcd (-a) b = gcd a b := by simp [gcd]
@[simp] theorem gcd_neg {a b : Int} : gcd a (-b) = gcd a b := by simp [gcd]

/-! ## lcm -/

/--
Computes the least common multiple of two integers as a natural number. The LCM of two integers is
the smallest natural number that's evenly divisible by the absolute values of both.

Examples:
 * `Int.lcm 9 6 = 18`
 * `Int.lcm 9 (-6) = 18`
 * `Int.lcm 9 3 = 9`
 * `Int.lcm 9 (-3) = 9`
 * `Int.lcm 0 3 = 0`
 * `Int.lcm (-3) 0 = 0`
-/
def lcm (m n : Int) : Nat := m.natAbs.lcm n.natAbs

theorem lcm_ne_zero (hm : m ≠ 0) (hn : n ≠ 0) : lcm m n ≠ 0 := by
  simp only [lcm]
  apply Nat.lcm_ne_zero <;> simpa

theorem dvd_lcm_left {a b : Int} : a ∣ lcm a b :=
  Int.dvd_trans dvd_natAbs_self (Int.ofNat_dvd.mpr (Nat.dvd_lcm_left a.natAbs b.natAbs))

theorem dvd_lcm_right {a b : Int} : b ∣ lcm a b :=
  Int.dvd_trans dvd_natAbs_self (Int.ofNat_dvd.mpr (Nat.dvd_lcm_right a.natAbs b.natAbs))

@[simp] theorem lcm_self {a : Int} : lcm a a = a.natAbs := Nat.lcm_self _

end Int
