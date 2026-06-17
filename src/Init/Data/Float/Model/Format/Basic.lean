/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julia M. Himmel
-/
module

prelude
public import Init.Data.Nat.Log2
public import Init.Data.Int.Basic

-- This file is part of the logical model for floats which authors of float libraries
-- need to rely on.
@[expose] public section

namespace Float.Model

/--
The position of the most significant digit, where the unit digit corresponds to `1`.
So, for example, `1.0b` has total exponent `1`, `0.1b` has total exponent `0`,
`0.01b` has total exponent `-1`, and so on.
-/
def totalExponent (mantissa : Nat) (exponent : Int) :=
  mantissa.log2 + 1 + exponent

/--
A floating point format is specified by two pieces of information: the number
of bits in the mantissa, and the number of bits in the exponent.
-/
structure Format where
  /-- The number of bits in the mantissa, *excluding the implicit bit*. -/
  mantissaBitsWithoutImplicit : Nat
  hm : 0 < mantissaBitsWithoutImplicit := by decide
  /-- The number of bits in the exponent. -/
  exponentBits : Nat
  he : 0 < exponentBits := by decide

namespace Format

/-- Specification corresponding to the IEEE `binary32` format. -/
abbrev binary32 : Format where
  mantissaBitsWithoutImplicit := 23
  exponentBits := 8

/-- Specification corresponding to the IEEE `binary64` format. -/
abbrev binary64 : Format where
  mantissaBitsWithoutImplicit := 52
  exponentBits := 11

/-- The total number of bits in the packed representation. -/
abbrev numBits (spec : Format) : Nat :=
  1 + spec.exponentBits + spec.mantissaBitsWithoutImplicit

/-- The number of bits in the mantissa, *including the implicit bit*. -/
def mantissaBits (spec : Format) : Nat :=
  1 + spec.mantissaBitsWithoutImplicit

/--
The exponent bias. In packed formats, we store the sum of the true exponent and
the bias.
-/
def exponentBias (spec : Format) : Nat :=
  2 ^ (spec.exponentBits - 1) - 1

/--
The smallest exponent possible for a number using the given specification,
including subnormals.
-/
def minExponent (spec : Format) : Int :=
  3 - 2 ^ (spec.exponentBits - 1) - spec.mantissaBits

/--
Suppose we have written a number where `totalExponent` is the position of the
most significant digit, where the unit digit corresponds to `1`. So, for example,
`1.0b` has total exponent `1`, `0.1b` has total exponent `0`, `0.01b` has total
exponent `-1`, and so on. This function computes which exponent that number
should have according to the given `Format`. So, for example, for the number
`0.1b` in `binary64` format, it wants us to use the exponent `-53`, corresponding
to the representation `2^52 * 2^(-53)`, which has a 53-bit mantissa. If the total
exponent gets quite small, then the result exponent eventually gets capped at
`spec.minExponent`, which first forces the result to be a subnormal number and
then, if the total exponent is even smaller, to be zero.
-/
def targetExponent (spec : Format) (totalExponent : Int) : Int :=
  max (totalExponent - spec.mantissaBits) spec.minExponent

end Format

end Float.Model
