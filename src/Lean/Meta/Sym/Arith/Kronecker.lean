/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Sym.Arith.Types
public section

namespace Lean.Meta.Sym.Arith
/-!
Parameters of the certificates by Kronecker substitution (`Init/Grind/Ring/Kronecker.lean`): the
elaborator side of the bounds that the kernel checks.
-/

/-- The degree bound `Grind.CommRing.Expr.degB_k` of `e`. -/
def exprDegB : RingExpr → Nat
  | .num _ | .natCast _ | .intCast _ => 0
  | .var _ => 1
  | .neg a => exprDegB a
  | .add a b | .sub a b => max (exprDegB a) (exprDegB b)
  | .mul a b => exprDegB a + exprDegB b
  | .pow a k => exprDegB a * k

/-- The coefficient bound `Grind.CommRing.Expr.majorant_k` of `e`. -/
def exprMajorant : RingExpr → Nat
  | .num k | .intCast k => k.natAbs
  | .natCast n => n
  | .var _ => 1
  | .neg a => exprMajorant a
  | .add a b | .sub a b => exprMajorant a + exprMajorant b
  | .mul a b => exprMajorant a * exprMajorant b
  | .pow a k => exprMajorant a ^ k

/-- The maximum degree of the monomials of `p` (`Grind.CommRing.Poly.maxDeg_k`). -/
def polyMaxDeg : Poly → Nat
  | .num _ => 0
  | .add _ m p => max m.degree (polyMaxDeg p)

/-- The sum of the absolute values of the coefficients of `p` (`Grind.CommRing.Poly.norm1_k`). -/
def polyNorm1 : Poly → Nat
  | .num k => k.natAbs
  | .add k _ p => k.natAbs + polyNorm1 p

/--
The exponent `K` of a Kronecker certificate over `n` variables with degrees below `B`, whose
coefficients are bounded by `norm`, if the values at the point stay below `maxBits` bits: they have
about `K * deg * B ^ (n - 1)` bits for the degree `deg`.
-/
def kronExponent? (norm deg B n maxBits : Nat) : Option Nat := Id.run do
  if (n - 1) * (Nat.log2 B + 1) > 24 then return none
  let K := (2 * norm).log2 + 1
  if K * (deg * B ^ (n - 1) + 1) > maxBits then return none
  return some K

end Lean.Meta.Sym.Arith
