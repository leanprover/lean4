/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Sym.Arith.Functions
public import Lean.Meta.Sym.Arith.MonadVar
public section
namespace Lean.Meta.Sym.Arith

/-!
# Denotation of reified expressions

Converts reified `RingExpr`, `Poly`, `Mon`, `Power` back into Lean `Expr`s using
the ring's cached operator functions and variable array.
-/

section Ring
variable [Monad m] [MonadError m] [MonadLiftT MetaM m] [MonadCanon m] [MonadRing m]

/-- Convert an integer to a numeral expression in the ring. Negative values use `getNegFn`. -/
def denoteNum (k : Int) : m Expr := do
  let ring ← getRing
  let n := mkRawNatLit k.natAbs
  let ofNatInst ← if let some inst ← MonadCanon.synthInstance? (mkApp2 (mkConst ``OfNat [ring.u]) ring.type n) then
    pure inst
  else
    pure <| mkApp3 (mkConst ``Grind.Semiring.ofNat [ring.u]) ring.type ring.semiringInst n
  let e := mkApp3 (mkConst ``OfNat.ofNat [ring.u]) ring.type n ofNatInst
  if k < 0 then
    return mkApp (← getNegFn) e
  else
    return e

/-- Denote a `Power` (variable raised to a power). -/
def denotePower [MonadGetVar m] (pw : Power) : m Expr := do
  let x ← getVar pw.x
  if pw.k == 1 then
    return x
  else
    return mkApp2 (← getPowFn) x (toExpr pw.k)

/-- Denote a `Mon` (product of powers). -/
def denoteMon [MonadGetVar m] (mn : Mon) : m Expr := do
  match mn with
  | .unit => denoteNum 1
  | .mult pw mn => go mn (← denotePower pw)
where
  go (mn : Mon) (acc : Expr) : m Expr := do
    match mn with
    | .unit => return acc
    | .mult pw mn => go mn (mkApp2 (← getMulFn) acc (← denotePower pw))

/-- Denote a `Poly` (sum of coefficient × monomial terms). -/
def denotePoly [MonadGetVar m] (p : Poly) : m Expr := do
  match p with
  | .num k => denoteNum k
  | .add k mn p => go p (← denoteTerm k mn)
where
  denoteTerm (k : Int) (mn : Mon) : m Expr := do
    if k == 1 then
      denoteMon mn
    else
      return mkApp2 (← getMulFn) (← denoteNum k) (← denoteMon mn)

  go (p : Poly) (acc : Expr) : m Expr := do
    match p with
    | .num 0 => return acc
    | .num k => return mkApp2 (← getAddFn) acc (← denoteNum k)
    | .add k mn p => go p (mkApp2 (← getAddFn) acc (← denoteTerm k mn))

@[specialize]
private def denoteRingExprCore (getVarExpr : Nat → m Expr) (e : RingExpr) : m Expr := do
  go e
where
  go : RingExpr → m Expr
  | .num k => denoteNum k
  | .natCast k => return mkApp (← getNatCastFn) (mkNatLit k)
  | .intCast k => return mkApp (← getIntCastFn) (mkIntLit k)
  | .var x => getVarExpr x
  | .add a b => return mkApp2 (← getAddFn) (← go a) (← go b)
  | .sub a b => return mkApp2 (← getSubFn) (← go a) (← go b)
  | .mul a b => return mkApp2 (← getMulFn) (← go a) (← go b)
  | .pow a k => return mkApp2 (← getPowFn) (← go a) (toExpr k)
  | .neg a => return mkApp (← getNegFn) (← go a)

/-- Denote a `RingExpr` whose variables are the current ring's, looked up with `getVar`. -/
def denoteRingExpr [MonadGetVar m] (e : RingExpr) : m Expr :=
  denoteRingExprCore getVar e

/--
Denote a `RingExpr` whose variables index `vars` instead of the current ring's variables.
Proof terms rename the variables of an expression to the compact range `0 .. n-1` of the
variables it actually uses (see `renameVars`), and build an `RArray` context out of those
`n` terms; the denotation of the renamed expression must use that same array.
-/
def denoteRingExpr' (vars : Array Expr) (e : RingExpr) : m Expr :=
  denoteRingExprCore (fun x => pure vars[x]!) e

end Ring

section Semiring
variable [Monad m] [MonadError m] [MonadLiftT MetaM m] [MonadCanon m] [MonadSemiring m]

/-- Convert a natural number to a numeral expression in the semiring. -/
def denoteNatNum (k : Nat) : m Expr := do
  let sr ← getSemiring
  let n := mkRawNatLit k
  let ofNatInst ← if let some inst ← MonadCanon.synthInstance? (mkApp2 (mkConst ``OfNat [sr.u]) sr.type n) then
    pure inst
  else
    pure <| mkApp3 (mkConst ``Grind.Semiring.ofNat [sr.u]) sr.type sr.semiringInst n
  return mkApp3 (mkConst ``OfNat.ofNat [sr.u]) sr.type n ofNatInst

/--
Denote a `SemiringExpr` whose variables index `vars`, using the semiring's operators.
Fails on the constructors that have no semiring denotation (`sub`, `neg`, `intCast`, negative numerals).
-/
def denoteSemiringExpr' (vars : Array Expr) (e : SemiringExpr) : m Expr :=
  go e
where
  go : SemiringExpr → m Expr
  | .num k =>
    if k < 0 then throwError "internal error: negative numeral in semiring expression" else denoteNatNum k.natAbs
  | .natCast k => return mkApp (← getNatCastFn') (mkNatLit k)
  | .var x => pure vars[x]!
  | .add a b => return mkApp2 (← getAddFn') (← go a) (← go b)
  | .mul a b => return mkApp2 (← getMulFn') (← go a) (← go b)
  | .pow a k => return mkApp2 (← getPowFn') (← go a) (toExpr k)
  | .sub .. | .neg .. | .intCast .. => throwError "internal error: ring operation in semiring expression"

end Semiring

end Lean.Meta.Sym.Arith
