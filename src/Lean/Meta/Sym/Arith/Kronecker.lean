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

/-- The packed code of `m` in base `B` (`Grind.CommRing.Mon.code_k`). -/
def monCode (B : Nat) : Mon → Nat
  | .unit => 0
  | .mult pw m => pw.k * B ^ pw.x + monCode B m

/-- The largest packed code of the monomials of `p`. -/
def polyMaxCode (B : Nat) : Poly → Nat
  | .num _ => 0
  | .add _ m p => max (monCode B m) (polyMaxCode B p)

/-- An upper bound on the packed codes of the monomials of the polynomials of `e` and its subterms. -/
def exprMaxCode (B : Nat) : RingExpr → Nat
  | .num _ | .natCast _ | .intCast _ => 0
  | .var x => B ^ x
  | .neg a => exprMaxCode B a
  | .add a b | .sub a b => max (exprMaxCode B a) (exprMaxCode B b)
  | .mul a b => exprMaxCode B a + exprMaxCode B b
  | .pow a k => exprMaxCode B a * k

/--
The exponent `K` of a Kronecker certificate whose coefficients are bounded by `norm` and whose
monomials have codes at most `maxCode`, if the values at the point stay below `maxBits` bits: they
have about `K * maxCode` bits.
-/
def kronExponent? (norm maxCode maxBits : Nat) : Option Nat :=
  if maxCode > maxBits then none else
  let K := (2 * norm).log2 + 1
  if K * (maxCode + 1) > maxBits then none else some K

/-- One more than the largest variable of `e`, the largest code of `Grind.CommRing.Expr.toLin`. -/
def exprMaxVar : RingExpr → Nat
  | .num _ | .natCast _ | .intCast _ => 0
  | .var x => x + 1
  | .neg a | .pow a _ => exprMaxVar a
  | .add a b | .sub a b | .mul a b => max (exprMaxVar a) (exprMaxVar b)

/--
The exponent `K` of the linear Kronecker certificate (`Grind.CommRing.Expr.eq_of_kronLin`) for
`l` and `r`, if they are linear and the values at the point stay below `maxBits` bits.
-/
def kronLinExponent? (l r : RingExpr) (maxBits : Nat) : Option Nat :=
  if exprDegB l ≤ 1 && exprDegB r ≤ 1 then
    kronExponent? (exprMajorant l + exprMajorant r) (max (exprMaxVar l) (exprMaxVar r)) maxBits
  else
    none

end Lean.Meta.Sym.Arith
