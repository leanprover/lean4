module

import Lean.Util.TestExtern
import Init.Data.UInt.Modular
import Init.Omega
import Init.WFTactics

/-!
Tests the modular `UInt64` operations. `mulMod` is compared against its native implementation;
`powMod` and `invMod?` are run by the compiler, which uses the `@[csimp]` implementations, and
compared against reference definitions that the compiler leaves alone.
-/

private def mulModRef (a b modulus : UInt64) : UInt64 :=
  .ofNat (a.toNat * b.toNat % modulus.toNat)

private def powModRef (base : UInt64) (exponent : Nat) (modulus : UInt64) : UInt64 :=
  if exponent = 0 then
    1 % modulus
  else
    let result := powModRef (mulModRef base base modulus) (exponent / 2) modulus
    if exponent % 2 = 1 then mulModRef result base modulus else result
termination_by exponent
decreasing_by omega

private def invModRef (a modulus : UInt64) : Option UInt64 :=
  if modulus = 0 then
    none
  else
    let rec go (oldR r oldS s : Nat) : Nat × Nat :=
      if _h : r = 0 then
        (oldR, oldS)
      else
        let product := oldR / r * s % modulus.toNat
        let nextS := if product ≤ oldS then oldS - product else modulus.toNat - (product - oldS)
        go r (oldR % r) s nextS
    termination_by r
    decreasing_by exact Nat.mod_lt _ (Nat.zero_lt_of_ne_zero _h)
    let (gcd, inverse) := go (a.toNat % modulus.toNat) modulus.toNat (1 % modulus.toNat) 0
    if gcd = 1 then some (.ofNat inverse) else none

private def values : List UInt64 :=
  [0, 1, 2, 3, 97, 0xffffffff, 0x100000000, 0x7fffffffffffffff, 0x8000000000000000,
    18446744073709551557, 0xfffffffffffffffe, 0xffffffffffffffff]

/-- Exponents on both sides of the scalar/big-`Nat` boundary and of the 64-bit chunk boundaries,
including exponents whose middle chunks are entirely zero. -/
private def exponents : List Nat :=
  [0, 1, 2, 31, 2 ^ 31, 2 ^ 63 - 1, 2 ^ 64 - 1, 2 ^ 64, 2 ^ 64 + 1, 2 ^ 128, 2 ^ 128 + 1,
    2 ^ 192 + 3, 2 ^ 64 * (2 ^ 64 + 1), 2 ^ 256 - 1, 2 ^ 320 + 7]

private def primes : List UInt64 := [97, 1000000007, 2147483647, 18446744073709551557]

test_extern UInt64.mulMod 0 0 0
test_extern UInt64.mulMod 18446744073709551615 18446744073709551615 0
test_extern UInt64.mulMod 18446744073709551615 18446744073709551615 1
test_extern UInt64.mulMod 18446744073709551615 18446744073709551615 18446744073709551557
test_extern UInt64.mulMod 1311768467463790320 1147797409030816545 18446744073709551557

private def mulModAgrees : Bool :=
  values.all fun a => values.all fun b => values.all fun m =>
    UInt64.mulMod a b m == mulModRef a b m

private def powModAgrees : Bool :=
  values.all fun base => values.all fun m => exponents.all fun e =>
    UInt64.powMod base e m == powModRef base e m

private def invModAgrees : Bool :=
  values.all fun a => values.all fun m => UInt64.invMod? a m == invModRef a m

/-- An inverse exists exactly when the arguments are coprime. -/
private def invModExists : Bool :=
  values.all fun a => values.all fun m =>
    m == 0 || (UInt64.invMod? a m).isSome == (Nat.gcd a.toNat m.toNat == 1)

/-- Every returned inverse is reduced and satisfies the defining equation. -/
private def invModSound : Bool :=
  values.all fun a => values.all fun m =>
    match UInt64.invMod? a m with
    | none => true
    | some x => x < m && a.toNat * x.toNat % m.toNat == 1 % m.toNat

/-- Fermat's little theorem, which does not depend on either implementation. -/
private def fermat : Bool :=
  primes.all fun p => values.all fun a =>
    a % p == 0 || UInt64.powMod a (p.toNat - 1) p == 1

#guard mulModAgrees
#guard powModAgrees
#guard invModAgrees
#guard invModExists
#guard invModSound
#guard fermat

#guard UInt64.mulMod 18446744073709551615 18446744073709551615 18446744073709551557 == 3364
#guard UInt64.powMod 3 18446744073709551616 97 == 61
#guard UInt64.invMod? 3 11 == some 4
#guard UInt64.invMod? 6 15 == none
#guard UInt64.invMod? 1 0 == none
