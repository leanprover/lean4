/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

prelude
public import Init.Data.UInt.Basic
import Init.Omega
import Init.WFTactics

@[expose] public section

namespace UInt64

/--
Multiplies two 64-bit unsigned integers and reduces the result modulo `modulus` without losing the
high half of the product. When `modulus` is `0`, the result is the wrapped product.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_uint64_mul_mod", implicit_reducible]
def mulMod (a b modulus : UInt64) : UInt64 :=
  .ofNat (a.toNat * b.toNat % modulus.toNat)

/--
Raises a 64-bit unsigned integer to a natural-number power modulo `modulus`, using
exponentiation by squaring. When `modulus` is `0`, the result is the wrapped power.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_uint64_pow_mod"]
def powMod (base : UInt64) (exponent : @& Nat) (modulus : UInt64) : UInt64 :=
  if exponent = 0 then
    1 % modulus
  else
    let result := powMod (mulMod base base modulus) (exponent / 2) modulus
    if exponent % 2 = 1 then mulMod result base modulus else result
termination_by exponent
decreasing_by omega

/--
Returns the multiplicative inverse of `a` modulo `modulus`, or `none` if the inverse does not
exist. For a nonzero modulus, an inverse exists exactly when `a` and `modulus` are coprime.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_uint64_inv_mod"]
def invMod? (a modulus : UInt64) : Option UInt64 :=
  if modulus = 0 then
    none
  else
    let rec go (oldR r oldS s : Nat) : Nat × Nat :=
      if _h : r = 0 then
        (oldR, oldS)
      else
        let quotient := oldR / r
        let product := quotient * s % modulus.toNat
        let nextS := if product ≤ oldS then oldS - product else modulus.toNat - (product - oldS)
        go r (oldR % r) s nextS
    termination_by r
    decreasing_by exact Nat.mod_lt _ (Nat.zero_lt_of_ne_zero _h)
    let (gcd, inverse) := go (a.toNat % modulus.toNat) modulus.toNat (1 % modulus.toNat) 0
    if gcd = 1 then some (.ofNat inverse) else none

end UInt64
