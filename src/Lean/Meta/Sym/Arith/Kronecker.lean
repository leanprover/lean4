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

/--
The estimates below saturate at `2 ^ kronSatBits`, which is larger than the bit limit of every
Kronecker certificate: an estimate that reaches it rejects the certificate (`kronExponent?`), and
the estimate is never computed in full. Without saturation, `((x - x) ^ 64) ^ 64 …` builds integers
of billions of bits.
-/
def kronSatBits : Nat := 2 ^ 22

/-- `a * b`, or a value of at least `2 ^ kronSatBits` if `a * b` is larger. -/
def satMul (a b : Nat) : Nat :=
  if a.log2 + b.log2 < kronSatBits then a * b else 2 ^ kronSatBits

/--
`a ^ k`, or a value of at least `2 ^ kronSatBits` if `a ^ k` is larger. A saturated `a` stays
saturated even for `k = 0`: the kernel still computes the estimate of the base.
-/
def satPow (a k : Nat) : Nat :=
  if kronSatBits ≤ a.log2 then a
  else if a ≤ 1 then a ^ k
  else if k * a.log2 < kronSatBits then a ^ k else 2 ^ kronSatBits

/-- The degree bound `Grind.CommRing.Expr.degB_k` of `e`. -/
def exprDegB : RingExpr → Nat
  | .num _ | .natCast _ | .intCast _ => 0
  | .var _ => 1
  | .neg a => exprDegB a
  | .add a b | .sub a b => max (exprDegB a) (exprDegB b)
  | .mul a b => exprDegB a + exprDegB b
  | .pow a k => exprDegB a * k

/-- `Grind.CommRing.Expr.lin_k e`: `exprDegB` with `|||` in place of the maximum. -/
def exprLin : RingExpr → Nat
  | .num _ | .natCast _ | .intCast _ => 0
  | .var _ => 1
  | .neg a => exprLin a
  | .add a b | .sub a b => exprLin a ||| exprLin b
  | .mul a b => exprLin a + exprLin b
  | .pow a k => exprLin a * k

/-- `Grind.CommRing.Expr.linS_k e`: `exprLin e`, or at least `2` if `e` is not a semiring term. -/
def exprLinS : RingExpr → Nat
  | .num k => if k ≥ 0 then 0 else 2
  | .natCast _ => 0
  | .var _ => 1
  | .intCast _ | .neg _ | .sub .. => 2
  | .add a b => exprLinS a ||| exprLinS b
  | .mul a b => exprLinS a + exprLinS b
  | .pow a k => let d := exprLinS a; if 2 ≤ d then 2 else d * k

/-- `Grind.CommRing.Expr.degS_k B e`: `exprDegB e`, or `B` if `e` is not a semiring term. -/
def exprDegS (B : Nat) : RingExpr → Nat
  | .num k => if k ≥ 0 then 0 else B
  | .natCast _ => 0
  | .var _ => 1
  | .intCast _ | .neg _ | .sub .. => B
  | .add a b => max (exprDegS B a) (exprDegS B b)
  | .mul a b => exprDegS B a + exprDegS B b
  | .pow a k => let d := exprDegS B a; if B ≤ d then B else d * k

/--
`true` if normalizing `e` multiplies out a sum: a product or power with a sum of nonconstant
terms. Otherwise normalizing `e` only merges terms, and is cheaper than a Kronecker certificate.
-/
def exprExpandsSum : RingExpr → Bool
  | .mul a b => (isSum a && exprDegB b ≥ 1) || (isSum b && exprDegB a ≥ 1) || exprExpandsSum a || exprExpandsSum b
  | .pow a k => (k ≥ 2 && isSum a) || exprExpandsSum a
  | .add a b | .sub a b => exprExpandsSum a || exprExpandsSum b
  | .neg a => exprExpandsSum a
  | _ => false
where
  isSum (e : RingExpr) : Bool := (e matches .add .. || e matches .sub ..) && exprDegB e ≥ 1

/-- The coefficient bound `Grind.CommRing.Expr.majorant_k` of `e`. -/
def exprMajorant : RingExpr → Nat
  | .num k | .intCast k => k.natAbs
  | .natCast n => n
  | .var _ => 1
  | .neg a => exprMajorant a
  | .add a b | .sub a b => exprMajorant a + exprMajorant b
  | .mul a b => satMul (exprMajorant a) (exprMajorant b)
  | .pow a k => satPow (exprMajorant a) k

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

/--
An upper bound on the packed codes of the monomials of the polynomials of `e` and its subterms.
The base of `a ^ 0` counts too, since the kernel evaluates it at the point.
-/
def exprMaxCode (B : Nat) : RingExpr → Nat
  | .num _ | .natCast _ | .intCast _ => 0
  | .var x => satPow B x
  | .neg a => exprMaxCode B a
  | .add a b | .sub a b => max (exprMaxCode B a) (exprMaxCode B b)
  | .mul a b => exprMaxCode B a + exprMaxCode B b
  | .pow a k => let c := exprMaxCode B a; if k = 0 then c else satMul c k

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
  if exprLin l ≤ 1 && exprLin r ≤ 1 then
    kronExponent? (exprMajorant l + exprMajorant r) (max (exprMaxVar l) (exprMaxVar r)) maxBits
  else
    none

/-- `Grind.CommRing.InvVars.lookup_k`: the search stops at the first larger variable. -/
def invLookup (invs : List (Var × Nat)) (x : Var) : Option Nat :=
  match invs with
  | [] => none
  | (y, c) :: invs => if x < y then none else if y == x then some c else invLookup invs x

/--
The coefficient bound and the denominator `Grind.CommRing.Expr.majQ_k` of `e`, where the variables
of `invs` denote the inverses of their numerals.
-/
def exprMajQ (invs : List (Var × Nat)) : RingExpr → Nat × Nat
  | .num k | .intCast k => (k.natAbs, 1)
  | .natCast n => (n, 1)
  | .var x => match invLookup invs x with
    | some c => (1, c)
    | none => (1, 1)
  | .neg a => exprMajQ invs a
  | .add a b | .sub a b =>
    let (m₁, d₁) := exprMajQ invs a
    let (m₂, d₂) := exprMajQ invs b
    (satMul m₁ d₂ + satMul m₂ d₁, satMul d₁ d₂)
  | .mul a b =>
    let (m₁, d₁) := exprMajQ invs a
    let (m₂, d₂) := exprMajQ invs b
    (satMul m₁ m₂, satMul d₁ d₂)
  | .pow a k =>
    let (m, d) := exprMajQ invs a
    (satPow m k, satPow d k)

/--
The arguments `K` and `B` of the Kronecker certificate of a field identity
(`Grind.CommRing.Expr.eq_of_kronQ`) for `l` and `r`, if the values stay below `maxBits` bits.
-/
def kronQArgs? (l r : RingExpr) (invs : List (Var × Nat)) (maxBits : Nat) : Option (Nat × Nat) :=
  let B := max 2 (max (deg l) (deg r) + 1)
  let (ml, dl) := exprMajQ invs l
  let (mr, dr) := exprMajQ invs r
  (kronExponent? (satMul dr ml + satMul dl mr) (max (go B l) (go B r)) maxBits).map (·, B)
where
  /-- `exprMaxCode`, where the variables of `invs` are constants. -/
  go (B : Nat) : RingExpr → Nat
    | .num _ | .natCast _ | .intCast _ => 0
    | .var x => if (invLookup invs x).isSome then 0 else satPow B x
    | .neg a => go B a
    | .add a b | .sub a b => max (go B a) (go B b)
    | .mul a b => go B a + go B b
    | .pow a k => let c := go B a; if k = 0 then c else satMul c k
  /-- `exprDegB`, where the variables of `invs` are constants (`Grind.CommRing.Expr.degQB_k`). -/
  deg : RingExpr → Nat
    | .num _ | .natCast _ | .intCast _ => 0
    | .var x => if (invLookup invs x).isSome then 0 else 1
    | .neg a => deg a
    | .add a b | .sub a b => max (deg a) (deg b)
    | .mul a b => deg a + deg b
    | .pow a k => deg a * k

/-- `Grind.CommRing.Expr.degQL_k`: `exprLin`, where the variables of `invs` are constants. -/
def exprDegQL (invs : List (Var × Nat)) : RingExpr → Nat
  | .num _ | .natCast _ | .intCast _ => 0
  | .var x => if (invLookup invs x).isSome then 0 else 1
  | .neg a => exprDegQL invs a
  | .add a b | .sub a b => exprDegQL invs a ||| exprDegQL invs b
  | .mul a b => exprDegQL invs a + exprDegQL invs b
  | .pow a k => exprDegQL invs a * k

/--
The exponent `K` of the linear field certificate (`Grind.CommRing.Expr.eq_of_kronQLin`) for `l`
and `r`, if they are linear in the variables not in `invs` and the values stay below `maxBits` bits.
-/
def kronQLinExponent? (l r : RingExpr) (invs : List (Var × Nat)) (maxBits : Nat) : Option Nat :=
  if exprDegQL invs l ≤ 1 && exprDegQL invs r ≤ 1 then
    let (ml, dl) := exprMajQ invs l
    let (mr, dr) := exprMajQ invs r
    kronExponent? (satMul dr ml + satMul dl mr) (max (maxVar l) (maxVar r)) maxBits
  else
    none
where
  /-- `exprMaxVar`, where the variables of `invs` are constants. -/
  maxVar : RingExpr → Nat
    | .num _ | .natCast _ | .intCast _ => 0
    | .var x => if (invLookup invs x).isSome then 0 else x + 1
    | .neg a | .pow a _ => maxVar a
    | .add a b | .sub a b | .mul a b => max (maxVar a) (maxVar b)

end Lean.Meta.Sym.Arith
