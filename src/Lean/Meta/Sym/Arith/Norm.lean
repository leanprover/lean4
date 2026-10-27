/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Sym.Arith.SafePoly
public import Lean.Meta.Sym.LitValues
public import Lean.Meta.Sym.Arith.DenoteExpr
public import Lean.Meta.Sym.Simp.Result
public import Lean.Meta.Sym.Canon
public import Lean.Meta.Sym.SynthInstance
public import Lean.Meta.Sym.Arith.Classify
public import Lean.Meta.Sym.Arith.VarRename
import Lean.Meta.Sym.Arith.ToExpr
public import Lean.Meta.Sym.Simp.App
import Lean.Meta.AppBuilder
public import Lean.Meta.NatInstTesters
public import Lean.Meta.Sym.AlphaShareBuilder
import Lean.Data.RArray
import Init.Grind.Norm
import Init.Grind.Ring.FieldSolver
import Init.Grind.Ring.IntSolver
public section
namespace Lean.Meta.Sym.Arith
open Lean.Meta.Sym.Simp (Result mkEqTransResult)
open Lean.Meta.Sym.Internal (mkAppS mkAppS₂)
open Lean.Grind.CommRing (PolyQ InvAtoms)
open Int.Internal.Linear (cdiv)

/-!
# Polynomial normalization of ring and semiring terms

`normalize?` rewrites a term of a `CommRing`, `Ring`, `CommSemiring`, or `Semiring` into the
polynomial normal form of `Poly.toExpr`, with a proof by reflection: the certificate compares
the `Init` polynomial of the input with the polynomial of the output (`Expr.eq_of_toPoly_eq`,
`Expr.eq_of_toPolyC_eq`, `eq_normS`, and their `_nc` variants for the non-commutative
structures, where monomials keep the order of their factors).

In a field of characteristic zero, the inverses of numerals are not atoms: the normal form is
`p * d⁻¹` with `p` an integer polynomial and `d` a numeral, in lowest terms, and a relation
becomes denominator-free (`a / 2 = b / 3` is `3 * a = 2 * b`). The certificate reifies `c⁻¹` as a
variable and eliminates it (`Expr.eq_of_toPolyQ_eq`, `Init/Grind/Ring/FieldSolver.lean`).
In any field, `x * x⁻¹` for an atom `x` is cancelled when the `discharge?` callback proves
`x ≠ 0` (`Expr.eq_of_cancelInvs_eq`); this is the only step whose result depends on the local
context, and it is marked `contextDependent`.

The normalizer owns the traversal of the arithmetic tree (`visit`): it recurses bottom-up
through the operators its structure interprets and hands every atom (maximal non-arithmetic
subterm) to the `simpAtom` callback, so that a simplifier can rewrite the atoms and the normal
form is stated for the simplified atoms. The congruence proof for that step is built with
`Sym.Simp.mkCongr`. Each node is reified once, and its polynomial is computed from its
children's with the `SafePoly` mirrors of the `toPoly` cases, so the polynomial of a node is the
kernel's `toPoly` of its reification by construction. A cast of a numeral (`↑(2 : Nat)`,
`↑(-2 : Int)`) is rewritten to the numeral of the carrier on the way, also when it is the whole
term, so that a numeral has one representation.

With `distrib := false`, a product of two non-constant polynomials is not expanded: its factors
are normalized and certified where they are, and the product is an atom (see `normalize?`).

A certificate (`certify`) numbers the atoms it mentions in `Expr.lt` order, so the normal form
of a term does not depend on the order in which its atoms occur, and two terms denoting the same
polynomial over the same atoms normalize to the same (maximally shared) expression.

The input is not assumed to be canonicalized. The instance of each operator is compared, after
`canonExpr`, with the structure's canonical one; a node with another instance is an atom. The
proof is stated for the original term, and the kernel closes the gap between the goal's
instances and the canonical ones of the output while checking the expected type, as it does for
`grind`.
-/

register_builtin_option sym.arith.maxTerms : Nat := {
  defValue := 64
  descr    := "maximum number of monomials of a polynomial produced by `Sym.Arith` normalization"
}

register_builtin_option sym.arith.maxDegree : Nat := {
  defValue := 64
  descr    := "maximum degree of a polynomial produced by `Sym.Arith` normalization"
}

/-- The algebraic structures supported by `normalize?`, with their `Sym.Arith` ids. -/
inductive Kind where
  | commRing (id : Nat)
  | commSemiring (id : Nat)
  /-- Non-commutative ring (`Sym.Arith.State.ncRings`). -/
  | ring (id : Nat)
  /-- Non-commutative semiring (`Sym.Arith.State.ncSemirings`). -/
  | semiring (id : Nat)
  deriving Inhabited

/-- `true` for (commutative or not) rings, `false` for semirings. -/
def Kind.isRing : Kind → Bool
  | .commRing _ | .ring _ => true
  | .commSemiring _ | .semiring _ => false

/-- `true` for the commutative structures. -/
def Kind.isComm : Kind → Bool
  | .commRing _ | .commSemiring _ => true
  | .ring _ | .semiring _ => false

structure NormM.Context where
  kind : Kind
  /-- See `normalize?`. -/
  distrib : Bool := true
  /-- The `PolyConfig` of the structure: characteristic, (non-)commutativity, and the budget options. -/
  polyCfg : PolyConfig := {}
  /-- `true` for a field of characteristic zero, where numeral inverses are rational coefficients. -/
  charZero : Bool := false

structure NormM.State where
  vars   : Array Expr := #[]
  varMap : PHashMap ExprPtr Var := {}
  /-- The variables `c⁻¹` for a numeral `c ≥ 1` with the field's `Inv` instance, with `c`. -/
  invVars : PHashMap Var Nat := {}
  /-- The side conditions `x ≠ 0` asked for so far, keyed by `x`, with the proof when discharged. -/
  invSideConds : PHashMap ExprPtr (Option Expr) := {}

abbrev NormM := ReaderT NormM.Context (StateRefT NormM.State SymM)

def getKind : NormM Kind :=
  return (← read).kind

instance : MonadCanon NormM where
  canonExpr e := do shareCommon (← Sym.canon e)
  synthInstance? e := Sym.synthInstance? e

instance : MonadCommRing NormM where
  getCommRing := do
    let .commRing id ← getKind | throwError "internal error: `Sym.Arith` normalizer is not in a commutative ring"
    return (← getArithState).rings[id]!
  modifyCommRing f := do
    let .commRing id ← getKind | throwError "internal error: `Sym.Arith` normalizer is not in a commutative ring"
    modifyArithState fun s => { s with rings := s.rings.modify id f }

instance : MonadCommSemiring NormM where
  getCommSemiring := do
    let .commSemiring id ← getKind | throwError "internal error: `Sym.Arith` normalizer is not in a commutative semiring"
    return (← getArithState).semirings[id]!
  modifyCommSemiring f := do
    let .commSemiring id ← getKind | throwError "internal error: `Sym.Arith` normalizer is not in a commutative semiring"
    modifyArithState fun s => { s with semirings := s.semirings.modify id f }

/-- Both ring kinds; takes precedence over the instance derived from `MonadCommRing`. -/
instance (priority := high) : MonadRing NormM where
  getRing := do
    match (← getKind) with
    | .commRing id => return (← getArithState).rings[id]!.toRing
    | .ring id => return (← getArithState).ncRings[id]!
    | _ => throwError "internal error: `Sym.Arith` normalizer is not in a ring"
  modifyRing f := do
    match (← getKind) with
    | .commRing id => modifyArithState fun s => { s with rings := s.rings.modify id fun r => { r with toRing := f r.toRing } }
    | .ring id => modifyArithState fun s => { s with ncRings := s.ncRings.modify id f }
    | _ => throwError "internal error: `Sym.Arith` normalizer is not in a ring"

/-- Both semiring kinds; takes precedence over the instance derived from `MonadCommSemiring`. -/
instance (priority := high) : MonadSemiring NormM where
  getSemiring := do
    match (← getKind) with
    | .commSemiring id => return (← getArithState).semirings[id]!.toSemiring
    | .semiring id => return (← getArithState).ncSemirings[id]!
    | _ => throwError "internal error: `Sym.Arith` normalizer is not in a semiring"
  modifySemiring f := do
    match (← getKind) with
    | .commSemiring id => modifyArithState fun s => { s with semirings := s.semirings.modify id fun r => { r with toSemiring := f r.toSemiring } }
    | .semiring id => modifyArithState fun s => { s with ncSemirings := s.ncSemirings.modify id f }
    | _ => throwError "internal error: `Sym.Arith` normalizer is not in a semiring"

instance : MonadMkVar NormM where
  mkVar e := do
    if let some x := (← get).varMap.find? { expr := e } then
      return x
    let x := (← get).vars.size
    modify fun s => { s with vars := s.vars.push e, varMap := s.varMap.insert { expr := e } x }
    return x

instance : MonadGetVar NormM where
  getVar x := return (← get).vars[x]!

/--
If `e` is an application of an arithmetic operator supported by the normalizer, or a cast of a
numeral, returns its carrier type.
-/
def getArithType? (e : Expr) : Option Expr :=
  match_expr e with
  | HAdd.hAdd α β γ _ _ _ => homoType? α β γ
  | HSub.hSub α β γ _ _ _ => homoType? α β γ
  | HMul.hMul α β γ _ _ _ => homoType? α β γ
  | HPow.hPow α β γ _ _ _ => if β.isConstOf ``Nat then homoType? α α γ else none
  | HSMul.hSMul σ α γ _ _ _ => if σ.isConstOf ``Nat || σ.isConstOf ``Int then homoType? α α γ else none
  | Neg.neg α _ _ => some α
  | HDiv.hDiv α β γ _ _ _ => homoType? α β γ
  | Inv.inv α _ _ => some α
  | NatCast.natCast α _ a => if (Sym.getNatValue? a).run.isSome then some α else none
  | IntCast.intCast α _ a => if (Sym.getIntValue? a).run.isSome then some α else none
  | _ => none

/-- `true` if the structure of `kind` is a field. -/
private def isFieldKind (kind : Kind) : SymM Bool := do
  let .commRing id := kind | return false
  return (← getArithState).rings[id]!.fieldInst?.isSome

/-!
## Rewrite steps

The steps applied by `visit` that are not congruences: `k • a ↦ ↑k * a`, casts of numerals, and
the field rewrites.
-/

section Visit
variable [Monad m] [MonadLiftT SymM m] [MonadLiftT MetaM m]

/--
Congruence step for `e := f a b`. `fa` is the subterm `f a` of `e`: a rebuilt `.app f a` would be
a fresh node, which is not maximally shared.
-/
private def congrBin (e fa f a b : Expr) (ra rb : Result) (h₁ : e = .app (.app f a) b) (h₂ : fa = .app f a) : m Result := do
  let r ← Simp.mkCongrArg fa f a ra h₂
  Simp.mkCongr e fa b r rb (h₂ ▸ h₁)

/--
The `k • a` rewrite hook: given `e₁ := k • a` (`k : Nat` or `Int`) whose `HSMul` instance is
the structure's, returns `↑k * a` with a proof of `e₁ = ↑k * a` by `Grind.smul_nat_eq_mul` /
`Grind.smul_int_eq_mul`. The kernel closes the gap between the instances of `e₁` and the
canonical ones while checking the expected type.
-/
private def mkSMulStep (kind : Kind) (isNat : Bool) (e₁ k a : Expr) : NormM (Expr × Expr) := do
  let (type, u, castFn, mulFn, thm) ← if kind.isRing then
      let ring ← getRing
      if isNat then
        pure (ring.type, ring.u, ← getNatCastFn, ← getMulFn, mkApp2 (mkConst ``Grind.smul_nat_eq_mul [ring.u]) ring.type ring.semiringInst)
      else
        pure (ring.type, ring.u, ← getIntCastFn, ← getMulFn, mkApp2 (mkConst ``Grind.smul_int_eq_mul [ring.u]) ring.type ring.ringInst)
    else
      let sr ← getSemiring
      pure (sr.type, sr.u, ← getNatCastFn', ← getMulFn', mkApp2 (mkConst ``Grind.smul_nat_eq_mul [sr.u]) sr.type sr.semiringInst)
  -- `↑k` is `k` itself when the scalar type is the carrier (`Nat` or `Int`); the cast is
  -- definitionally the identity there, and the kernel unfolds it in the expected-type check.
  let k' := if type.isConstOf (if isNat then ``Nat else ``Int) then k else mkApp castFn k
  let e₂ ← share (mkApp2 mulFn k' a)
  return (e₂, mkExpectedPropHint (mkApp2 thm k a) (mkApp3 (mkConst ``Eq [u.succ]) type e₁ e₂))

/--
The cast rewrite hook: given `e := ↑k` for a numeral `k : Nat`, or `k : Int` in a ring, whose
cast instance is the structure's, returns the numeral `k` of the carrier with a proof of `e = k`
by `Grind.Semiring.natCast_eq_ofNat` / `Grind.Ring.intCast_eq_ofNat_of_nonneg` /
`Grind.Ring.intCast_eq_ofNat_of_nonpos`. Returns `none` when the instance is a different one;
`e` is then an atom.
-/
private def mkCastLitStep? (kind : Kind) (e : Expr) : NormM (Option (Expr × Expr)) := do
  match_expr e with
  | NatCast.natCast _ _ a =>
    let some k := (Sym.getNatValue? a).run | return none
    let (type, u, castFn, semiringInst) ← if kind.isRing then
        let ring ← getRing
        pure (ring.type, ring.u, ← getNatCastFn, ring.semiringInst)
      else
        let sr ← getSemiring
        pure (sr.type, sr.u, ← getNatCastFn', sr.semiringInst)
    unless isSameExpr castFn (← canonExpr e.appFn!) do return none
    let e₂ ← share (← if kind.isRing then denoteNum k else denoteNatNum k)
    let thm := mkApp3 (mkConst ``Grind.Semiring.natCast_eq_ofNat [u]) type semiringInst a
    return some (e₂, mkExpectedPropHint thm (mkApp3 (mkConst ``Eq [u.succ]) type e e₂))
  | IntCast.intCast _ _ a =>
    unless kind.isRing do return none
    let some k := (Sym.getIntValue? a).run | return none
    unless isSameExpr (← getIntCastFn) (← canonExpr e.appFn!) do return none
    let ring ← getRing
    let e₂ ← share (← denoteNum k)
    let thmName := if k < 0 then ``Grind.Ring.intCast_eq_ofNat_of_nonpos else ``Grind.Ring.intCast_eq_ofNat_of_nonneg
    let thm := mkApp4 (mkConst thmName [ring.u]) ring.type ring.ringInst a eagerReflBoolTrue
    return some (e₂, mkExpectedPropHint thm (mkApp3 (mkConst ``Eq [ring.u.succ]) ring.type e e₂))
  | _ => return none

/-!
Field rewrites applied by the walk, all without side conditions (`Init/Grind/Ring/Field.lean`):
`a / b ↦ a * b⁻¹`, `(a * b)⁻¹ ↦ a⁻¹ * b⁻¹`, `(a ^ n)⁻¹ ↦ a⁻¹ ^ n`, `(-a)⁻¹ ↦ -a⁻¹`, `a⁻¹⁻¹ ↦ a`,
`0⁻¹ ↦ 0`, `1⁻¹ ↦ 1`. After them, `x⁻¹` for an atom or numeral `x` is an atom of the
polynomial; the certificate eliminates numeral inverses in characteristic zero (`getInvVars`)
and cancels `x * x⁻¹` under a discharged `x ≠ 0` (`decideInvAtoms`).
-/

private def mkFieldStep (thm : Expr) (e₁ e₂ : Expr) : NormM (Expr × Expr) := do
  let ring ← getCommRing
  let e₂ ← share e₂
  return (e₂, mkExpectedPropHint thm (mkApp3 (mkConst ``Eq [ring.u.succ]) ring.type e₁ e₂))

/-- `a / b = a * b⁻¹` -/
private def mkDivStep (e a b : Expr) : NormM (Expr × Expr) := do
  let ring ← getCommRing
  let thm := mkApp4 (mkConst ``Grind.Field.div_eq_mul_inv [ring.u]) ring.type ring.fieldInst?.get! a b
  mkFieldStep thm e (mkApp2 (← getMulFn) a (mkApp (← getInvFn) b))

/--
The inverse rewrites, for `e := x⁻¹` with the field's `Inv` instance. `(a * b)⁻¹` and `(a ^ n)⁻¹`
are only rewritten with `distrib`; otherwise they are atoms, like the products they invert.
-/
private def mkInvStep? (e x : Expr) : NormM (Option (Expr × Expr)) := do
  let ring ← getCommRing
  let fieldInst := ring.fieldInst?.get!
  let invFn ← getInvFn
  let distrib := (← read).distrib
  let thm (name : Name) : Expr := mkApp2 (mkConst name [ring.u]) ring.type fieldInst
  match_expr x with
  | HMul.hMul _ _ _ _ a b =>
    unless distrib do return none
    unless isSameExpr (← getMulFn) (← canonExpr x.appFn!.appFn!) do return none
    return some (← mkFieldStep (mkApp2 (thm ``Grind.Field.inv_mul) a b) e (mkApp2 (← getMulFn) (mkApp invFn a) (mkApp invFn b)))
  | HPow.hPow _ _ _ _ a k =>
    unless distrib do return none
    unless (Sym.getNatValue? k).run.isSome do return none
    unless isSameExpr (← getPowFn) (← canonExpr x.appFn!.appFn!) do return none
    return some (← mkFieldStep (mkApp2 (thm ``Grind.Field.inv_pow) a k) e (mkApp2 (← getPowFn) (mkApp invFn a) k))
  | Neg.neg _ _ a =>
    unless isSameExpr (← getNegFn) (← canonExpr x.appFn!) do return none
    return some (← mkFieldStep (mkApp (thm ``Grind.Field.inv_neg) a) e (mkApp (← getNegFn) (mkApp invFn a)))
  | Inv.inv _ _ a =>
    unless isSameExpr invFn (← canonExpr x.appFn!) do return none
    return some (← mkFieldStep (mkApp (thm ``Grind.Field.inv_inv) a) e a)
  | OfNat.ofNat _ _ _ =>
    match (Sym.getNatValue? x).run with
    | some 0 => return some (← mkFieldStep (thm ``Grind.Field.inv_zero) e (← denoteNum 0))
    | some 1 => return some (← mkFieldStep (thm ``Grind.Field.inv_one) e (← denoteNum 1))
    | _ => return none
  | _ => return none

end Visit

/-! ## Certificate helpers -/

/--
The `Field` and `IsCharP _ 0` instances when the structure is a field of characteristic zero,
where numeral inverses become rational coefficients (`Init/Grind/Ring/FieldSolver.lean`).
-/
private def fieldChar0? : NormM (Option (Expr × Expr)) := do
  let .commRing _ ← getKind | return none
  let ring ← getCommRing
  let some fieldInst := ring.fieldInst? | return none
  let some (charInst, 0) := ring.charInst? | return none
  return some (fieldInst, charInst)

/--
The numeral-inverse atoms among `vars`: `(x, c)` for `vars[x] = c⁻¹` with the field's `Inv`
instance and a numeral `c ≥ 1`. As for the numerals of the polynomial, the `OfNat` instance is
not checked; the kernel closes the gap while checking the expected type.
-/
private def getInvVars (vars : Array Expr) : NormM (Array (Var × Nat)) := do
  let invFn ← getInvFn
  let mut invs := #[]
  for (e, x) in vars.zipIdx do
    let_expr Inv.inv _ _ n := e | continue
    unless isSameExpr invFn (← canonExpr e.appFn!) do continue
    let some c := (Sym.getNatValue? n).run | continue
    if c > 0 then invs := invs.push (x, c)
  return invs

/-- `true` if some monomial of `p` contains both `x` and `y`. -/
private def sharesMonomial (p : Poly) (x y : Var) : Bool :=
  match p with
  | .num _ => false
  | .add _ m p => (m.degreeOf x > 0 && m.degreeOf y > 0) || sharesMonomial p x y

/--
The inverse pairs among the atoms: `(y, x)` for `vars[y] = vars[x]⁻¹` with the field's `Inv`
instance and some monomial of `p` containing both. The side conditions `vars[x] ≠ 0` are decided
by `decideInvAtoms`.
-/
private def invAtomPairs (vars : Array Expr) (p : Poly) : NormM (Array (Var × Var)) := do
  let invFn ← getInvFn
  let mut result := #[]
  for (e, y) in vars.zipIdx do
    let_expr Inv.inv _ _ n := e | continue
    unless isSameExpr invFn (← canonExpr e.appFn!) do continue
    let some x := vars.findIdx? (isSameExpr · n) | continue
    unless sharesMonomial p x y do continue
    result := result.push (y, x)
  return result

/-- The `InvAtoms` list of the pairs. -/
private def invAtomsList (ainvs : Array (Var × Var × Expr)) : InvAtoms :=
  ainvs.toList.map fun (y, x, _) => (y, x)

/-- `InvAtoms.ok ctx ainvs`: `x * x⁻¹ = 1` by `Field.mul_inv_cancel` from `h : x ≠ 0` for each pair. -/
private def mkInvAtomsOk (ring : CommRing) (ctx : Expr) (vars : Array Expr) (ainvs : Array (Var × Var × Expr)) : Expr :=
  go ainvs.toList
where
  go : List (Var × Var × Expr) → Expr
    | [] => mkConst ``True.intro
    | (y, x, h) :: l =>
      let hxy := mkApp4 (mkConst ``Grind.Field.mul_inv_cancel [ring.u]) ring.type ring.fieldInst?.get! vars[x]! h
      mkApp8 (mkConst ``Grind.CommRing.InvAtoms.ok_cons [ring.u]) ring.type ring.ringInst ctx (toExpr y) (toExpr x)
        (toExpr (invAtomsList l.toArray)) hxy (go l)

/-- `InvVars.ok ctx invs` by `Eq.refl`: the kernel evaluates both denotation lists. -/
private def mkInvVarsOk (type : Expr) (u : Level) (ctx invsE : Expr) : Expr :=
  mkApp2 (mkConst ``Eq.refl [u.succ]) (mkApp (mkConst ``List [u]) type)
    (mkApp3 (mkConst ``Grind.CommRing.InvVars.denoteVars [u]) type ctx invsE)

/--
The reified normal form of `q = num / den`: `num * d⁻¹`, where the atom `d⁻¹` is appended to
`vars` and `invs` unless already present; `num` alone when `den = 1`, `d⁻¹` alone when
`num = 1`.
-/
private def mkPolyQExpr (q : PolyQ) (vars : Array Expr) (invs : Array (Var × Nat)) :
    NormM (RingExpr × Array Expr × Array (Var × Nat)) := do
  if q.den == 1 then return (q.num.toExpr, vars, invs)
  let invD ← share (mkApp (← getInvFn) (← denoteNum q.den))
  let x := (vars.findIdx? (isSameExpr · invD)).getD vars.size
  let vars := if x == vars.size then vars.push invD else vars
  let invs := if invs.any (·.1 == x) then invs else invs.push (x, q.den)
  let re := if q.num == .num 1 then .var x else .mul q.num.toExpr (.var x)
  return (re, vars, invs)

private inductive CoreResult where
  /-- The structure does not interpret the root (an atom, or an operator with another instance). -/
  | notApplicable
  /-- The term is already in normal form. -/
  | normal
  /-- The term normalizes to `e'` with proof `h`. -/
  | step (e' h : Expr)

/--
The `RArray` context of the variables `vars`. An empty context holds `(↑0 : α)`, built only in that
case, so the `natCast` operator is initialized only when needed.
-/
private def mkContext (type : Expr) (vars : Array Expr) : NormM Expr := do
  if h : 0 < vars.size then
    RArray.toExpr type id (RArray.ofFn (vars[·]) h)
  else
    let natCastFn ← if (← getKind).isRing then getNatCastFn else getNatCastFn'
    RArray.toExpr type id (RArray.leaf (mkApp natCastFn (mkNatLit 0)))

/-- The `PolyConfig` of the structure: characteristic, (non-)commutativity, and the budget options. -/
private def polyConfig : NormM PolyConfig := do
  let kind ← getKind
  let char? ← match kind with
    | .commRing _ | .ring _ =>
      pure ((← getRing).charInst?.bind fun (_, c) => if c != 0 then some c else none)
    | _ => pure none
  let opts ← getOptions
  return {
    char?
    semiring := !kind.isRing
    commutative := kind.isComm
    maxTerms? := some (sym.arith.maxTerms.get opts)
    maxDegree? := some (sym.arith.maxDegree.get opts)
  }

/-!
## Visiting the arithmetic tree

`visit` traverses the arithmetic tree of `e` (the nodes the structure interprets, by head symbol
and canonical instance) bottom-up. It simplifies the atoms with `simpAtom`, reifies each node
once, computes its polynomial from its children's, and, with `distrib := false`, keeps a product
of non-constant polynomials as an atom after normalizing its factors.
-/

/--
A visited arithmetic subterm `e`. Example, with `simpAtom` rewriting `f x` to `x` and
`distrib := false`:
```
e  := (f x + 1 + 0) + (2 + f x) + f x * (1 + y + 1)
e₁ := (x + 1 + 0) + (2 + x) + x * (y + 2)
re := .add (.add (.add (.add (.var a) (.num 1)) (.num 0)) (.add (.num 2) (.var a))) (.var c)
p  := 2 * a + c + 3
```
`e₁` is `e` after `simpAtom` rewrote its atoms and the kept products were normalized: the three
`f x` became `x` (`simpAtom` only sees the maximal non-arithmetic subterms `f x` and `y`), and
in the kept product `f x * (1 + y + 1)` the factor `1 + y + 1` became `y + 2`, because `keep`
certifies the factors of a product before making it an atom. `r` proves `e = e₁`. In `re`, the
atoms `x` and `y` are the variables `a` and `b`, and the kept product `x * (y + 2)` is the
variable `c`. `p` is `toPoly re`. `certify` then proves
`e₁ = 2 * x + x * (y + 2) + 3`, the denotation of `p` up to the order of the monomials. With
`distrib := true`, the last summand is reified as
`.mul (.var a) (.add (.add (.num 1) (.var b)) (.num 1))` and `p` is `a * b + 4 * a + 3`.
-/
private structure Node where
  /-- `e = e₁`, where `e₁` is `e` with its atoms simplified and its kept products normalized. -/
  r : Result
  /-- The reification of `e₁` over the variables of the run. -/
  re : RingExpr
  /-- `toPoly re`, over the same variables. -/
  p : Poly
  /--
  `true` if `e₁` is a node kept as an atom with its subterms normalized (a product or power with
  `distrib := false`, a node over the budget, or an operator with another instance): it is in
  normal form.
  -/
  kept : Bool := false
  deriving Inhabited

/-- The callbacks of `normalize?`. -/
private structure Visitor (m : Type → Type) where
  simpAtom : Expr → m Result
  discharge? : Expr → m (Option Expr)

/--
The visitor's monad: `NormM` over the caller's monad `m`, so that the atoms are simplified and
the side conditions discharged in `m` while the variables are shared by the whole run.
-/
private abbrev VisitM (m : Type → Type) := ReaderT NormM.Context (StateT NormM.State m)

section Visit
variable [Monad m] [MonadLiftT SymM m] [MonadLiftT MetaM m]

/-- Runs a `NormM` computation on the current context and state. -/
private def liftNorm (x : NormM α) : VisitM m α := fun ctx s => do
  (x.run ctx).run s

/-- Runs a polynomial computation with the structure's configuration. -/
private def runPoly (x : PolyM α) : VisitM m (Option α) := do
  x.run (← read).polyCfg

/-- Chains `r₁ : e = e₁` with `r₂`, a result for `e₁`; `done` is `r₂`'s. -/
private def chainResults (e e₁ : Expr) (r₁ r₂ : Result) : SymM Result := do
  match r₁ with
  | .rfl _ cd₁ =>
    match r₂ with
    | .rfl done cd₂ => return .rfl done (cd₁ || cd₂)
    | .step e' h done cd₂ => return .step e' h done (cd₁ || cd₂)
  | .step _ h₁ _ cd₁ => mkEqTransResult e e₁ h₁ r₂ cd₁

/--
`e = e'` by `Eq.refl e'`, for a cast `e` and the same cast `e'` with the canonical instance. The
kernel closes the gap while checking the expected type, as it does for the instances of the output.
-/
private def mkDefEqStep (e e' : Expr) : NormM Result := do
  let (type, u) ← if (← getKind).isRing then
      let ring ← getRing; pure (ring.type, ring.u)
    else
      let sr ← getSemiring; pure (sr.type, sr.u)
  return .step e' (mkExpectedPropHint (mkApp2 (mkConst ``Eq.refl [u.succ]) type e') (mkApp3 (mkConst ``Eq [u.succ]) type e e'))

/--
The node of the atom `e₁` (the simplified atom, or a kept product), with `r : e = e₁`. A cast
with another instance (e.g., `Semiring.natCast` from a generic rewrite rule) is the atom with the
canonical cast, so that it is the same atom as a canonical `↑a`.
-/
private def mkAtom (e₁ : Expr) (r : Result) (kept := false) : VisitM m Node := do
  let (e₁, r) ← if e₁.isAppOfArity ``NatCast.natCast 3 || e₁.isAppOfArity ``IntCast.intCast 3 then
      liftNorm do
        let f ← canonExpr e₁.appFn!
        if isSameExpr f e₁.appFn! then pure (e₁, r)
        else
          let e₂ ← mkAppS f e₁.appArg!
          pure (e₂, ← chainResults e₁ e₂ r (← mkDefEqStep e₁ e₂))
    else pure (e₁, r)
  let x ← liftNorm do
    let x ← mkVar e₁
    if (← read).charZero then
      if let .app invF c := e₁ then
        if isSameExpr (← getInvFn) (← canonExpr invF) then
          if let some k := (Sym.getNatValue? c).run then
            if k > 0 then modify fun s => { s with invVars := s.invVars.insert x k }
    return x
  return { r, re := .var x, p := .ofVar x, kept }

/-- `true` for `k` and `k * m`: polynomials with at most one monomial and no constant. -/
private def isMonomial : Poly → Bool
  | .num _ => true
  | .add _ _ (.num 0) => true
  | _ => false

private def allInvVars (invVars : PHashMap Var Nat) : Mon → Bool
  | .unit => true
  | .mult pw m => invVars.contains pw.x && allInvVars invVars m

/--
`true` if `p` is a scalar: a constant, or in a field of characteristic zero a constant times
inverses of numerals (`3`, `4⁻¹`, `3 * (2⁻¹ * 5⁻¹)`; not `2 * x` or `x⁻¹`), which the normal form
turns into a rational coefficient.
-/
private def isScalar (p : Poly) : VisitM m Bool := do
  match p with
  | .num _ => return true
  | .add _ m (.num 0) => return (← read).charZero && allInvVars (← get).invVars m
  | _ => return false

/--
With `distrib := false`, the product of the polynomials `pa` and `pb` is expanded only when one
is a scalar or both are monomials; any other product is an atom whose factors are normalized
separately.
-/
private def expandMul (pa pb : Poly) : VisitM m Bool := do
  if (← read).distrib then return true
  if (← isScalar pa) then return true
  if (← isScalar pb) then return true
  return isMonomial pa && isMonomial pb

/-- The structure's canonical function for the operator, for the ring or semiring kind. -/
private def opFn (ring semiring : NormM Expr) : VisitM m Expr := do
  liftNorm do if (← getKind).isRing then ring else semiring

/-- `true` if `pre` (`HAdd.hAdd α α α inst`, ...) is the structure's canonical function `fn` for the operator. -/
private def isInst (fn pre : Expr) : VisitM m Bool := do
  if isSameExpr fn pre then return true
  return isSameExpr fn (← liftNorm (canonExpr pre))

end Visit

/-!
## Certificates

`certify` turns a visited node into the proof that its term equals the denotation of its
polynomial, by reflection on the `Init` polynomial functions (`Expr.eq_of_toPoly_eq` and
variants). It renames the variables of the node to a compact range in `Expr.lt` order, so each
certificate only touches its own atoms.
-/

/--
Renames the variables of `m` with `f`. In a commutative structure the variables of a monomial are
in ascending order and are sorted again; in a non-commutative one they are the factors in order.
-/
private def renameMon (m : Mon) (f : Grind.VarRename) (commutative : Bool) : Mon :=
  let pws := go m #[]
  let pws := if commutative then pws.qsort fun a b => a.x < b.x else pws
  pws.foldr (fun pw m => .mult pw m) .unit
where
  go : Mon → Array Power → Array Power
    | .unit, acc => acc
    | .mult pw m, acc => go m (acc.push { pw with x := f pw.x })

/-- Renames the variables of `p` with `f`, keeping its monomials in `grevlex` order. -/
private def renamePoly (p : Poly) (f : Grind.VarRename) (commutative : Bool) : Poly :=
  let (terms, c) := go p #[]
  let terms := terms.qsort fun (_, m₁) (_, m₂) => m₁.grevlex m₂ == .gt
  terms.foldr (fun (k, m) p => .add k m p) (.num c)
where
  go : Poly → Array (Int × Mon) → Array (Int × Mon) × Int
    | .num c, acc => (acc, c)
    | .add k m p, acc => go p (acc.push (k, renameMon m f commutative))

/-- The compact `Expr.lt`-ordered variables of `re`: the renaming and the renamed variable array. -/
private def compactVars (re : RingExpr) : NormM (Grind.VarRename × Array Expr) := do
  let vars := (← get).vars
  let used := Std.HashSet.toArray (re.collectVars {}) |>.qsort fun i j => Expr.lt vars[i]! vars[j]!
  return (Grind.mkVarRename used, used.map (vars[·]!))

/-- The number of summands of the sum or difference `e`, and the largest such number in `e`. -/
private def summands : RingExpr → Nat × Nat
  | .add a b | .sub a b =>
    let (n₁, m₁) := summands a
    let (n₂, m₂) := summands b
    (n₁ + n₂, max (n₁ + n₂) (max m₁ m₂))
  | .neg a => summands a
  | .mul a b =>
    let (_, m₁) := summands a
    let (_, m₂) := summands b
    (1, max m₁ m₂)
  | .pow a _ => (1, (summands a).2)
  | _ => (1, 1)

/-- The number of monomial comparisons of `Poly.combine p₁ p₂`. -/
private partial def combineSteps (p₁ p₂ : Poly) (n : Nat := 0) : Nat :=
  match p₁, p₂ with
  | .add _ m₁ q₁, .add _ m₂ q₂ =>
    match m₁.grevlex m₂ with
    | .gt => combineSteps q₁ p₂ (n + 1)
    | .lt => combineSteps p₁ q₂ (n + 1)
    | .eq => combineSteps q₁ q₂ (n + 1)
  | _, _ => n

/--
Kernel cost model of the certificates: the number of monomial comparisons made by the additions
of `Expr.toPoly_k` (`steps`), and those of `Expr.toPolyB_k` together with the number of polynomials
it adds as lists (`balSteps`, `items`).
-/
private structure CertCost where
  steps : Nat := 0
  balSteps : Nat := 0
  items : Nat := 0

/-- `Poly.sumB_k`: adds `ps` pairwise, level by level, counting the comparisons in `n`. -/
private partial def sumBSteps (ps : List Poly) (n : Nat) : Poly × Nat :=
  match ps with
  | [] => (.num 0, n)
  | [p] => (p, n)
  | _ =>
    let rec pairs : List Poly → Array Poly → Nat → Array Poly × Nat
      | a :: b :: ps, acc, n => pairs ps (acc.push (a.combine b)) (n + combineSteps a b)
      | [a], acc, n => (acc.push a, n)
      | [], acc, n => (acc, n)
    let (ps, n) := pairs ps #[] n
    sumBSteps ps.toList n

/-- The partial products of `p₁ * p₂`, as `Poly.mulTerms_k`. -/
private def mulTerms (p₁ p₂ : Poly) : List Poly :=
  match p₁ with
  | .num k => [p₂.mulConst k]
  | .add k m p₁ => p₂.mulMon k m :: mulTerms p₁ p₂

/-- `Poly.mul p₁ p₂` (`Poly.mul_k`), and its comparisons added to `n`. -/
private def mulSteps (p₁ p₂ : Poly) (n : Nat) : Poly × Nat :=
  (mulTerms p₁ p₂).foldl (init := (.num 0, n)) fun (acc, n) q => (acc.combine q, n + combineSteps acc q)

/-- `Poly.mulB_k p₁ p₂`, its comparisons added to `n`, and its partial products added to `items`. -/
private def mulBSteps (p₁ p₂ : Poly) (n items : Nat) : Poly × Nat × Nat :=
  match p₁, p₂ with
  | .num k, _ => (p₂.mulConst k, n, items)
  | _, .num k => (p₁.mulConst k, n, items)
  | .add k m (.num 0), _ => (p₂.mulMon k m, n, items)
  | _, .add k m (.num 0) => (p₁.mulMon k m, n, items)
  | _, _ =>
    let ts := mulTerms p₁ p₂
    let (p, n) := sumBSteps ts n
    (p, n, items + ts.length)

/-- The polynomial of the numeral, variable or power `a ^ k` when `a` is a numeral or variable. -/
private def powAtom? (a : RingExpr) (k : Nat) : Option Poly :=
  if k == 0 then some (.num 1) else
  match a with
  | .num n | .intCast n => some (.num (n ^ k))
  | .natCast n => some (.num ((n : Int) ^ k))
  | .var x => some (.ofMon (.mult { x, k } .unit))
  | _ => none

/-- The polynomial of `e` and the comparisons of `Expr.toPoly_k` (`Poly.mul`, `Poly.pow`), added to `n`. -/
private def oldSteps (e : RingExpr) (n : Nat) : Poly × Nat :=
  match e with
  | .num k | .intCast k => (.num k, n)
  | .natCast k => (.num k, n)
  | .var x => (.ofVar x, n)
  | .neg a => let (p, n) := oldSteps a n; (p.mulConst (-1), n)
  | .add a b =>
    let (pa, n) := oldSteps a n
    let (pb, n) := oldSteps b n
    (pa.combine pb, n + combineSteps pa pb)
  | .sub a b =>
    let (pa, n) := oldSteps a n
    let (pb, n) := oldSteps b n
    let pb := pb.mulConst (-1)
    (pa.combine pb, n + combineSteps pa pb)
  | .mul a b =>
    let (pa, n) := oldSteps a n
    let (pb, n) := oldSteps b n
    mulSteps pa pb n
  | .pow a k =>
    if let some p := powAtom? a k then (p, n) else
    let (pa, n) := oldSteps a n
    (List.range (k - 1)).foldl (init := (pa, n)) fun (acc, n) _ => mulSteps pa acc n

/--
The summands of `e` (negated if `neg`) prepended to `acc`, as `Expr.sumsB_k`, with the
comparisons and the polynomials added as lists by `Expr.toPolyB_k`.
-/
private partial def balSummands (e : RingExpr) (neg : Bool) (acc : List Poly) (n items : Nat) : List Poly × Nat × Nat :=
  match e with
  | .add a b =>
    let (acc, n, items) := balSummands b neg acc n items
    balSummands a neg acc n items
  | .sub a b =>
    let (acc, n, items) := balSummands b (!neg) acc n items
    balSummands a neg acc n items
  | .neg a => balSummands a (!neg) acc n items
  | _ =>
    let (p, n, items) := balLeaf e n items
    ((if neg then p.mulConst (-1) else p) :: acc, n, items + 1)
where
  /-- The polynomial of a summand, which is not a sum, difference or negation. -/
  balLeaf (e : RingExpr) (n items : Nat) : Poly × Nat × Nat :=
    match e with
    | .num k | .intCast k => (.num k, n, items)
    | .natCast k => (.num k, n, items)
    | .var x => (.ofVar x, n, items)
    | .mul a b =>
      let (pa, n, items) := balPoly a n items
      let (pb, n, items) := balPoly b n items
      mulBSteps pa pb n items
    | .pow a k =>
      if let some p := powAtom? a k then (p, n, items) else
      let (pa, n, items) := balPoly a n items
      (List.range (k - 1)).foldl (init := (pa, n, items)) fun (acc, n, items) _ => mulBSteps pa acc n items
    | _ => (.num 0, n, items)
  /-- `Expr.toPolyB_k`. -/
  balPoly (e : RingExpr) (n items : Nat) : Poly × Nat × Nat :=
    let (ps, n, items) := balSummands e false [] n items
    let (p, n) := sumBSteps ps n
    (p, n, items)

/-- The cost model of the certificates for `e`. -/
private def certCost (e : RingExpr) : CertCost :=
  let (_, steps) := oldSteps e 0
  let (_, balSteps, items) := balSummands.balPoly e 0 0
  { steps, balSteps, items }

/--
`true` if the kernel should compute the polynomial of `re` with `Expr.toPolyB_k` instead of
`Expr.toPoly_k`. Adding the summands of a sum one at a time costs a quadratic number of monomial
comparisons when each summand goes at the end of the polynomial, and the partial products of
large multiplications have the same issue, but the balanced additions cost extra kernel steps per
polynomial they add as a list. Small polynomials (`size` monomials) and short sums use
`Expr.toPoly_k`; otherwise the comparisons of both are counted. A comparison costs about the same
kernel time in both, and a polynomial added as a list about half a comparison.
-/
private def useBalanced (re : RingExpr) (size : Nat) : Bool :=
  if size < 32 && (summands re).2 < 12 then false else
  let c := certCost re
  2 * c.balSteps + c.items < 2 * c.steps

/--
The certificate for `e₁` reified as `re` with polynomial `p`, both over the compact variables
`vars`; `ainvs` are the inverse pairs with discharged side conditions, over the same variables.
Returns `.normal` when `e₁` is already the denotation of `p`.
-/
private def mkCertificate (e₁ : Expr) (re : RingExpr) (p : Poly) (vars : Array Expr) (ainvs : Array (Var × Var × Expr)) : NormM CoreResult := do
  let kind ← getKind
  -- `inst` is the structure instance the certificate theorem takes: `CommRing`, `Ring`,
  -- `CommSemiring`, or `Semiring`.
  let (type, u, inst, char?) ← match kind with
    | .commRing _ =>
      let ring ← getCommRing
      let char? := ring.charInst?.bind fun (inst, c) => if c != 0 then some (inst, c) else none
      pure (ring.type, ring.u, ring.commRingInst, char?)
    | .ring _ =>
      let ring ← getRing
      let char? := ring.charInst?.bind fun (inst, c) => if c != 0 then some (inst, c) else none
      pure (ring.type, ring.u, ring.ringInst, char?)
    | .commSemiring _ =>
      let sr ← getCommSemiring
      pure (sr.type, sr.u, sr.commSemiringInst, none)
    | .semiring _ =>
      let sr ← getSemiring
      pure (sr.type, sr.u, sr.semiringInst, none)
  -- Fields: inverse atoms with a discharged side condition are cancelled, and in
  -- characteristic zero the numeral inverses become rational coefficients.
  let fc? ← fieldChar0?
  let invs ← if fc?.isSome then getInvVars vars else pure #[]
  let ainvsL := invAtomsList ainvs
  let (re', vars, invs) ←
    if !invs.isEmpty then mkPolyQExpr (p.toPolyQ invs.toList ainvsL) vars invs
    else if !ainvs.isEmpty then pure ((p.cancelInvs ainvsL).toExpr, vars, invs)
    else pure (p.toExpr, vars, invs)
  let e' ← if kind.isRing then share (← denoteRingExpr' vars re') else share (← denoteSemiringExpr' vars re')
  if isSameExpr e' e₁ then
    return .normal
  let ctx ← mkContext type vars
  let hoka ← if ainvs.isEmpty then pure (mkConst ``True.intro) else pure (mkInvAtomsOk (← getCommRing) ctx vars ainvs)
  let ainvsE := toExpr ainvsL
  let h ← if !invs.isEmpty then
    let (fieldInst, charInst) := fc?.get!
    let invsE := toExpr invs.toList
    let thm := mkApp3 (mkConst ``Grind.CommRing.Expr.eq_of_toPolyQ_eq [u]) type fieldInst charInst
    pure (mkAppN thm #[ctx, toExpr (useBalanced re p.length), invsE, mkInvVarsOk type u ctx invsE, ainvsE, hoka,
      toExpr re, toExpr re', eagerReflBoolTrue])
  else if !ainvs.isEmpty then
    let thm := mkApp2 (mkConst ``Grind.CommRing.Expr.eq_of_cancelInvs_eq [u]) type inst
    pure (mkApp6 thm ctx ainvsE hoka (toExpr re) (toExpr re') eagerReflBoolTrue)
  else if kind matches .commRing _ then
    -- `p = re.toPolyX_k bal` (`re.toPolyC_k c`) and `re' = p.toExpr_k`, both checked by
    -- definitional equality.
    let thm := match char? with
      | some (charInst, c) =>
        mkApp6 (mkConst ``Grind.CommRing.Expr.eq_of_toPolyC_eq_toExpr [u]) type (toExpr c) inst charInst ctx (toExpr (useBalanced re p.length))
      | none =>
        mkApp4 (mkConst ``Grind.CommRing.Expr.eq_of_toPolyX_eq_toExpr [u]) type inst ctx (toExpr (useBalanced re p.length))
    let pE := toExpr p
    let re'E := toExpr re'
    pure (mkApp5 thm (toExpr re) re'E pE
      (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Grind.CommRing.Poly) pE)
      (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Grind.CommRing.Expr) re'E))
  else if kind matches .commSemiring _ then
    -- `p = re.toPolyS_k` and `re' = p.toExpr_k`, both checked by definitional equality.
    let thm := mkApp4 (mkConst ``Grind.CommRing.Expr.eq_of_toPolyS_eq_toExpr [u]) type inst ctx (toExpr (useBalanced re p.length))
    let pE := toExpr p
    let re'E := toExpr re'
    pure (mkApp5 thm (toExpr re) re'E pE
      (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Grind.CommRing.Poly) pE)
      (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Grind.CommRing.Expr) re'E))
  else
    let thm := match kind, char? with
      | .commRing _, some (charInst, c) => mkApp4 (mkConst ``Grind.CommRing.Expr.eq_of_toPolyC_eq [u]) type (toExpr c) inst charInst
      | .commRing _, none => mkApp2 (mkConst ``Grind.CommRing.Expr.eq_of_toPoly_eq [u]) type inst
      | .ring _, some (charInst, c) => mkApp4 (mkConst ``Grind.CommRing.Expr.eq_of_toPolyC_nc_eq [u]) type (toExpr c) inst charInst
      | .ring _, none => mkApp2 (mkConst ``Grind.CommRing.Expr.eq_of_toPoly_nc_eq [u]) type inst
      | .commSemiring _, _ => mkApp2 (mkConst ``Grind.CommRing.eq_normS [u]) type inst
      | .semiring _, _ => mkApp2 (mkConst ``Grind.CommRing.eq_normS_nc [u]) type inst
    pure (mkApp4 thm ctx (toExpr re) (toExpr re') eagerReflBoolTrue)
  return .step e' (mkExpectedPropHint h (mkApp3 (mkConst ``Eq [u.succ]) type e₁ e'))

section Visit
variable [Monad m] [MonadLiftT SymM m] [MonadLiftT MetaM m]

/--
The inverse pairs of `p` over the run's variables whose side condition `vars[x] ≠ 0` is
discharged, as `(y, x, h)`. A side condition is asked for once per `x` (`invSideConds`), so the
flag is `true` when one was asked for now, whatever the outcome: the result then depends on the
local context.
-/
private def decideInvAtoms (v : Visitor m) (p : Poly) : VisitM m (Array (Var × Var × Expr) × Bool) := do
  unless (← liftNorm do isFieldKind (← getKind)) do return (#[], false)
  let vars := (← get).vars
  let pairs ← liftNorm (invAtomPairs vars p)
  let mut result := #[]
  let mut asked := false
  for (y, x) in pairs do
    let n := vars[x]!
    let h? ← match (← get).invSideConds.find? { expr := n } with
      | some h? => pure h?
      | none =>
        asked := true
        let ring ← liftNorm getRing
        let prop := mkApp3 (mkConst ``Ne [ring.u.succ]) ring.type n (← liftNorm (denoteNum 0))
        let h? ← v.discharge? prop
        modify fun s => { s with invSideConds := s.invSideConds.insert { expr := n } h? }
        pure h?
    if let some h := h? then result := result.push (y, x, h)
  return (result, asked)

/--
The proof `e₁ = e'` that the visited node `n` of `e₁` equals its normal form `e'`, `done`. For a
kept node `e'` is `e₁` itself; for a plain atom the result is `.rfl` without `done`, so that a
simplifier still visits its subterms.
-/
private def certify (v : Visitor m) (e₁ : Expr) (n : Node) : VisitM m Result := do
  if n.re matches .var _ then return .rfl (done := n.kept)
  let (ainvs, cd) ← decideInvAtoms v n.p
  let r ← liftNorm do
    let (f, vars) ← compactVars n.re
    let ainvs := ainvs.map fun (y, x, h) => (f y, f x, h)
    mkCertificate e₁ (n.re.renameVars f) (renamePoly n.p f (← read).polyCfg.commutative) vars ainvs
  match r with
  | .notApplicable => return .rfl (contextDependent := cd)
  | .normal => return .rfl (done := true) (contextDependent := cd)
  | .step e' h => return .step e' h (done := true) (contextDependent := cd)

/-- `certify` chained with the node's own result: the proof `e = e'` for the subterm `e` visited as `n`. -/
private def normalizeNode (v : Visitor m) (e : Expr) (n : Node) : VisitM m Result := do
  let e₁ := n.r.getResultExpr e
  chainResults e e₁ n.r (← certify v e₁ n)

/-- The node of `e₂`, a term `e` was rewritten to with `r₁ : e = e₂`. -/
private def chainNode (e e₂ : Expr) (r₁ : Result) (n : Node) : VisitM m Node := do
  return { n with r := (← chainResults e e₂ r₁ n.r) }

/-- The node for the structure's numeral `k` at `e₁`, with `r : e = e₁`. -/
private def numNode (e₁ : Expr) (r : Result) (k : Int) : VisitM m Node := do
  let some p ← runPoly (SafePoly.numNode k) | mkAtom e₁ r
  return { r, re := .num k, p }

/-- `true` if `visit` interprets the head of `e`: an arithmetic operator, a cast of a numeral, or a numeral. -/
private def isInterpreted (e : Expr) : Bool :=
  (getArithType? e).isSome || e.isAppOfArity ``OfNat.ofNat 3 || e.isAppOfArity ``BitVec.ofNat 2

private partial def visit (v : Visitor m) (e : Expr) : VisitM m Node := do
  let kind := (← read).kind
  let isRing := kind.isRing
  -- An atom: simplified by `simpAtom`; its result is visited when it is a term the structure
  -- interprets (e.g., `3#8` evaluates to the numeral `3`, `f x` unfolds to `x + 1`).
  let atom : VisitM m Node := do
    let r ← v.simpAtom e
    let e₁ := r.getResultExpr e
    if !isSameExpr e₁ e && isInterpreted e₁ then
      chainNode e e₁ r (← visit v e₁)
    else
      mkAtom e₁ r
  -- A product or power kept as an atom: its factors are normalized where they are.
  let keep (fa f a b : Expr) (ra rb : Result) (h₁ : e = .app (.app f a) b) (h₂ : fa = .app f a) : VisitM m Node := do
    let r ← congrBin e fa f a b ra rb h₁ h₂
    mkAtom (r.getResultExpr e) r (kept := true)
  -- An interpreted operator with another instance is an atom; its arguments are still normalized.
  -- `simpAtom` must not visit `e` itself: `simp` would re-enter `e` through `normalizeTerm?`.
  let unexpected : VisitM m Unit := do
    reportIssue! "ring term with unexpected instance{indentExpr e}"
  let unexpectedBin (fa f a b : Expr) (na nb : Node) (h₁ : e = .app (.app f a) b) (h₂ : fa = .app f a) : VisitM m Node := do
    unexpected
    keep fa f a b (← normalizeNode v a na) (← normalizeNode v b nb) h₁ h₂
  -- A binary node with the visited children `na`, `nb`, reified as `re` with polynomial `p`.
  -- Over the budget, the node is an atom whose children are normalized, like a kept product.
  let binNode (fa f a b : Expr) (na nb : Node) (re : RingExpr) (p : PolyM Poly)
      (h₁ : e = .app (.app f a) b) (h₂ : fa = .app f a) : VisitM m Node := do
    match (← runPoly p) with
    | some p =>
      let r ← congrBin e fa f a b na.r nb.r h₁ h₂
      return { r, re, p }
    | none => keep fa f a b (← normalizeNode v a na) (← normalizeNode v b nb) h₁ h₂
  -- A binary node: `mk` builds the reification, `op` the polynomial, from the children's.
  let bin (fn : Expr) (mk : RingExpr → RingExpr → RingExpr) (op : Poly → Poly → PolyM Poly) : VisitM m Node := do
    match h : e with
    | .app fa@h':(.app f a) b =>
      let na ← visit v a
      let nb ← visit v b
      unless (← isInst fn f) do return (← unexpectedBin fa f a b na nb h h')
      binNode fa f a b na nb (mk na.re nb.re) (op na.p nb.p) h h'
    | _ => unreachable!
  -- Metadata is transparent to the kernel and `grind` never internalizes it, so an annotated node
  -- (e.g., an inaccessible pattern of a `match` equation) is normalized without the annotation.
  -- Note that `match_expr` ignores metadata, but the structural matches below do not.
  if let .mdata _ b := e then
    let n ← visit v b
    let r ← match n.r with
      | .rfl _ cd => pure (Result.step b (← Sym.mkEqRefl b) (contextDependent := cd))
      | r => pure r
    return { n with r }
  match_expr e with
  | HAdd.hAdd _ _ _ _ _ _ => bin (← opFn getAddFn getAddFn') .add SafePoly.combine
  | HMul.hMul _ _ _ _ _ _ =>
    match h : e with
    | .app fa@h':(.app f a) b =>
      let na ← visit v a
      let nb ← visit v b
      unless (← isInst (← opFn getMulFn getMulFn') f) do return (← unexpectedBin fa f a b na nb h h')
      if (← expandMul na.p nb.p) then
        binNode fa f a b na nb (.mul na.re nb.re) (SafePoly.mul na.p nb.p) h h'
      else
        keep fa f a b (← normalizeNode v a na) (← normalizeNode v b nb) h h'
    | _ => unreachable!
  | HSub.hSub _ _ _ _ _ _ =>
    unless isRing do return (← atom)
    bin (← liftNorm getSubFn) .sub fun pa pb => do SafePoly.combine pa (← SafePoly.mulConst (-1) pb)
  | Neg.neg _ _ _ =>
    unless isRing do return (← atom)
    match h : e with
    | .app f a =>
      let na ← visit v a
      let ok ← isInst (← liftNorm getNegFn) f
      unless ok do unexpected
      match (← if ok then runPoly (SafePoly.mulConst (-1) na.p) else pure none) with
      | some p =>
        -- A negative numeral is reified as `.num (-k)`, the form the normalizer renders it
        -- in, so that `-1 = x` is recognized as an equation between a numeral and an atom.
        -- `-0` stays `.neg (.num 0)`: `.num 0` denotes to `0`, which is not `-0` in a general ring.
        let re := match na.re with
          | .num k => if k == 0 then .neg na.re else .num (-k)
          | re => .neg re
        return { r := (← Simp.mkCongrArg e f a na.r h), re, p }
      | none =>
        let r ← Simp.mkCongrArg e f a (← normalizeNode v a na) h
        mkAtom (r.getResultExpr e) r (kept := true)
    | _ => unreachable!
  | HPow.hPow _ _ _ _ _ k =>
    -- Only literal exponents are interpreted; the exponent is not simplified.
    let some kv := (Sym.getNatValue? k).run | atom
    match h : e with
    | .app fa@h':(.app f a) k =>
      let na ← visit v a
      let ok ← isInst (← opFn getPowFn getPowFn') f
      unless ok do unexpected
      -- With `distrib := false`, only a monomial is raised to a power. The exponent is not a
      -- node of the structure, so the power is kept directly when it is over the budget.
      let expand := ok && ((← read).distrib || isMonomial na.p)
      match (← if expand then runPoly (SafePoly.powNode na.re na.p kv) else pure none) with
      | some p => return { r := ← congrBin e fa f a k na.r .rfl h h', re := .pow na.re kv, p }
      | none => keep fa f a k (← normalizeNode v a na) .rfl h h'
    | _ => unreachable!
  | HSMul.hSMul σ _ _ _ _ _ =>
    let isNat := σ.isConstOf ``Nat
    unless isNat || (isRing && σ.isConstOf ``Int) do return (← atom)
    -- The instance must be the structure's `nsmul`/`zsmul`; compare the canonicalized prefix.
    let fn ← liftNorm do match kind.isRing, isNat with
      | true, true => getNatSMulFn
      | true, false => getIntSMulFn
      | false, _ => getNatSMulFn'
    unless (← isInst fn e.appFn!.appFn!) do return (← atom)
    match h : e with
    | .app fk@h':(.app f k) a =>
      -- The scalar is an atom of its own type; `k • a` is then `↑k * a`, visited as such.
      let r₁ ← congrBin e fk f k a (← v.simpAtom k) .rfl h h'
      let e₁ := r₁.getResultExpr e
      let (e₂, h₂) ← liftNorm (mkSMulStep kind isNat e₁ e₁.appFn!.appArg! e₁.appArg!)
      let r₁ ← chainResults e e₁ r₁ (.step e₂ h₂)
      chainNode e e₂ r₁ (← visit v e₂)
    | _ => unreachable!
  | HDiv.hDiv _ _ _ _ a b =>
    unless (← liftNorm (isFieldKind kind)) do return (← atom)
    unless (← isInst (← liftNorm getDivFn) e.appFn!.appFn!) do return (← atom)
    let (e₂, h) ← liftNorm (mkDivStep e a b)
    chainNode e e₂ (.step e₂ h) (← visit v e₂)
  | Inv.inv _ _ _ =>
    unless (← liftNorm (isFieldKind kind)) do return (← atom)
    unless (← isInst (← liftNorm getInvFn) e.appFn!) do return (← atom)
    -- Simplify `x` (a proper subterm, so `simp` normalizes it without re-entering `e`),
    -- then rewrite `x'⁻¹`.
    match h : e with
    | .app f x =>
      let r ← Simp.mkCongrArg e f x (← v.simpAtom x) h
      let e₁ := r.getResultExpr e
      match (← liftNorm (mkInvStep? e₁ e₁.appArg!)) with
      | some (e₂, h₁) =>
        let r ← chainResults e e₁ r (.step e₂ h₁)
        chainNode e e₂ r (← visit v e₂)
      | none => mkAtom e₁ r
    | _ => unreachable!
  | NatCast.natCast _ _ a =>
    let some k := (Sym.getNatValue? a).run | atom
    -- A cast of a numeral becomes the numeral of the carrier. With a different cast instance, it is
    -- an atom, but one `simpAtom` must not visit: `simp` would re-enter `e` through `normalizeTerm?`.
    let some (e₂, h) ← liftNorm (mkCastLitStep? kind e) | mkAtom e .rfl
    numNode e₂ (.step e₂ h) k
  | IntCast.intCast _ _ a =>
    unless isRing do return (← atom)
    let some k := (Sym.getIntValue? a).run | atom
    let some (e₂, h) ← liftNorm (mkCastLitStep? kind e) | mkAtom e .rfl
    numNode e₂ (.step e₂ h) k
  | OfNat.ofNat _ n _ =>
    -- `Sym.canon` leaves a raw literal here; anything else is an atom. The `OfNat` instance is
    -- not checked: the certificate denotes the canonical numeral, and the kernel closes the gap.
    let .lit (.natVal k) := n | mkAtom e .rfl
    numNode e .rfl k
  | BitVec.ofNat _ n =>
    let .lit (.natVal k) := n | atom
    numNode e .rfl k
  | _ => atom

end Visit

/-! ## Relations

`lhs = rhs`, `lhs ≤ rhs`, `lhs < rhs` over a ring or semiring are normalized by
moving everything to one side and splitting by sign (`x + y = z + 2 * x` becomes `y = z + x`),
or, with `lhsOnly`, by keeping everything on the left (`y + -1 * z + -1 * x = 0`).
With `lhsOnly`, an equation `k * m + k' = 0` or `k * m₁ = k * m₂` over a commutative ring of
nonzero characteristic `c` is solved for the monomial when `k` is invertible modulo `c`
(`eq_norm_mul_exprC`): in `Fin 5`, `4 * x + 2 = 0` becomes `x = 2`.
Rings use `eq_norm_expr`, `le_norm_expr`, `lt_norm_expr` (`CommSolver.lean`); in a field of
characteristic zero the numerator of `lhs - rhs` is split instead (`eq_normQ_expr`,
`le_normQ_expr`, `lt_normQ_expr` in `FieldSolver.lean`, the last two under `IsLinearOrder`), so
the result has no numeral inverses; inverse atoms with a discharged side condition are cancelled
(`eq_normA_expr`, `le_normA_expr`, `lt_normA_expr`). Semirings have no
subtraction: both sides are normalized as terms after removing their common part `c`
(`eq_normS` twice, the relation between `lhs' + c` and `rhs' + c` by congruence), and `c` is
cancelled with `AddRightCancel.add_right_cancel_iff`, `OrderedAdd.add_le_left_iff`, or
`OrderedAdd.add_lt_left_iff`.
-/

inductive RelKind where
  | eq | le | lt
  deriving Inhabited, BEq

/--
Positive monomials, negated negative monomials, and the constant of `p`. With a nonzero
characteristic `c` the coefficients of `p` lie in `[0, c)`, so a coefficient above `c / 2` is
read as the negative `k - c` (balanced residue), otherwise everything would land on one side.
-/
private def splitPoly (char? : Option Nat) (p : Poly) : Poly × Poly × Int :=
  let neg? (k : Int) : Option Int := match char? with
    | none => if k < 0 then some (-k) else none
    | some c => if k > c / 2 then some (c - k) else none
  match p with
  | .num k => (.num 0, .num 0, (neg? k).map (- ·) |>.getD k)
  | .add k m p =>
    let (l, r, c) := splitPoly char? p
    match neg? k with
    | some k' => (l, .add k' m r, c)
    | none => (.add k m l, r, c)

/-- Monomial-wise minimum of two polynomials with nonnegative coefficients: the part they share. -/
private partial def commonPart : Poly → Poly → Poly
  | .num a, .num b => .num (min a b)
  | .num a, .add _ _ q => commonPart (.num a) q
  | .add _ _ p, .num b => commonPart p (.num b)
  | .add k₁ m₁ p, .add k₂ m₂ q =>
    match m₁.grevlex m₂ with
    | .eq => .add (min k₁ k₂) m₁ (commonPart p q)
    | .gt => commonPart p (.add k₂ m₂ q)
    | .lt => commonPart (.add k₁ m₁ p) q

/--
The ring relation theorem for `rel`: the `_nc` variant for non-commutative rings, the `C`
variant for a nonzero characteristic. Spelled out so that a renamed theorem is caught when
this file is compiled.
-/
private def relThmName (rel : RelKind) (comm : Bool) (char : Bool) : Name :=
  match rel, comm, char with
  | .eq, true,  false => ``Grind.CommRing.eq_norm_expr
  | .eq, true,  true  => ``Grind.CommRing.eq_norm_exprC
  | .eq, false, false => ``Grind.CommRing.eq_norm_expr_nc
  | .eq, false, true  => ``Grind.CommRing.eq_norm_exprC_nc
  | .le, true,  false => ``Grind.CommRing.le_norm_expr
  | .le, true,  true  => ``Grind.CommRing.le_norm_exprC
  | .le, false, false => ``Grind.CommRing.le_norm_expr_nc
  | .le, false, true  => ``Grind.CommRing.le_norm_exprC_nc
  | .lt, true,  false => ``Grind.CommRing.lt_norm_expr
  | .lt, true,  true  => ``Grind.CommRing.lt_norm_exprC
  | .lt, false, false => ``Grind.CommRing.lt_norm_expr_nc
  | .lt, false, true  => ``Grind.CommRing.lt_norm_exprC_nc

private def mkIffSymm (a b h : Expr) : Expr :=
  mkApp3 (mkConst ``Iff.symm) a b h

private def mkPropExt (a b h : Expr) : Expr :=
  mkApp3 (mkConst ``propext) a b h

/-- The constant of `p`. -/
private def polyConst : Poly → Int
  | .num k => k
  | .add _ _ p => polyConst p

/-- The gcd of the monomial coefficients of `p` (without the constant); `0` for a constant. -/
private def gcdMonCoeffs (p : Poly) : Nat :=
  go p 0
where
  go : Poly → Nat → Nat
    | .num _, g => g
    | .add k _ p, g => let g := Nat.gcd g k.natAbs; if g == 1 then 1 else go p g

/-- Divides the monomial coefficients of `p` by `k` and drops the constant. -/
private def divMonCoeffs (k : Nat) : Poly → Poly
  | .num _ => .num 0
  | .add c m p => .add (c / k) m (divMonCoeffs k p)

/-- Extended Euclid. Invariant: `r₀ ≡ t₀ * k` and `r₁ ≡ t₁ * k` modulo `c`. -/
private partial def modInvGo (c : Nat) (r₀ r₁ t₀ t₁ : Int) : Option Int :=
  if r₁ == 0 then
    if r₀ == 1 then some (t₀ % c) else none
  else
    let q := r₀ / r₁
    modInvGo c r₁ (r₀ - q * r₁) t₁ (t₀ - q * t₁)

/-- The inverse of `k` modulo `c`, in `[0, c)`, when `k` and `c` are coprime. -/
private def modInv? (k : Int) (c : Nat) : Option Int :=
  modInvGo c c (k % c) 0 1

/--
The leading coefficient `k` of `p` when `p` is `k * m + k'` or `k * m₁ - k * m₂` in
characteristic `c`: the shapes for which `p = 0` is solved for a monomial by multiplying with
the inverse of `k`.
-/
private def solvableCoeff? (c : Nat) : Poly → Option Int
  | .add k _ (.num _) => some k
  | .add k₁ _ (.add k₂ _ (.num 0)) => if k₁ + k₂ == c then some k₁ else none
  | _ => none

/-- `p` is a numeral or a single variable: the sides of the equations `simp +arith` leaves alone. -/
private def isNumOrAtom : Poly → Bool
  | .num _ => true
  | .add 1 (.mult ⟨_, 1⟩ .unit) (.num 0) => true
  | _ => false

/--
Given the reified sides `l`, `r` of `e := rel lhs rhs`, with their polynomials `pl`, `pr` and the
variables `vars` they index (compact, in `Expr.lt` order), returns the normalized relation.
`relFn` is the canonical `Eq α`/`LE.le α inst`/`LT.lt α inst`, `order?` the order classification,
required for `≤` and `<`, and `ainvs` the inverse pairs of `pl - pr` with their discharged side
conditions (`decideInvAtoms`), for rings.
-/
private def normalizeRelCore (rel : RelKind) (relFn : Expr) (order? : Option Order) (e lhs rhs : Expr)
    (l r : RingExpr) (pl pr : Poly) (vars : Array Expr) (ainvs : Array (Var × Var × Expr)) (lhsOnly : Bool) : NormM CoreResult := do
  let kind ← getKind
  let budget := (← read).polyCfg
  if kind.isRing then
    let ring ← getRing
    let u := ring.u
    -- Instance for the certificate theorem: `CommRing` or `Ring`.
    let inst ← if kind.isComm then pure (← getCommRing).commRingInst else pure ring.ringInst
    let char? := ring.charInst?.bind fun (inst, c) => if c != 0 then some (inst, c) else none
    let some p ← (do SafePoly.combine pl (← SafePoly.mulConst (-1) pr) : PolyM Poly).run budget | return .notApplicable
    -- Fields: cancel the discharged inverse atoms; in characteristic zero, split the numerator
    -- of `lhs - rhs`, whose denominator's sign needs `IsLinearOrder` for `≤`/`<`.
    let fc? ← fieldChar0?
    let mut invs ← if fc?.isSome then getInvVars vars else pure #[]
    let ainvsL := invAtomsList ainvs
    let linInst? ← if invs.isEmpty || rel == .eq then pure none else
      MonadCanon.synthInstance? (mkApp2 (mkConst ``Std.IsLinearOrder [u]) ring.type order?.get!.leInst)
    if rel != .eq && linInst?.isNone then invs := #[]
    -- `simp +arith` leaves equations between atoms and numerals alone (`x = y`, `x = 3`,
    -- `3 = x`): `grind` and other tactics handle these directly. The sides are classified by
    -- their polynomials, so `2 * 3 - 7 = x` is `-1 = x` and `(7 : Fin 5) = x` is `2 = x`; they
    -- are rendered below without solving for a side. With inverse atoms, the sides must go
    -- through the field normalization below.
    let numOrAtom := lhsOnly && rel == .eq && invs.isEmpty && ainvs.isEmpty && isNumOrAtom pl && isNumOrAtom pr
    let p := if !invs.isEmpty then (p.toPolyQ invs.toList ainvsL).num
      else if !ainvs.isEmpty then p.cancelInvs ainvsL
      else p
    -- `Int`: like `simp +arith`, divide the coefficients by their gcd `k` (`p = k * q + c`).
    -- An equation whose constant is not divisible by `k` is `False`, and `≤` is tightened by
    -- rounding the constant up. `<` is left to the `Int.lt_eq` rewrite. `tight?` records
    -- `(q, k, c)` for the certificate (`IntSolver.lean`).
    let mut p := p
    let mut tight? : Option (Poly × Int × Int) := none
    if ring.type.isConstOf ``Int && invs.isEmpty && ainvs.isEmpty && char?.isNone && rel != .lt && !numOrAtom then
      let k := gcdMonCoeffs p
      if k > 1 then
        let c := polyConst p
        let q := divMonCoeffs k p
        if rel == .eq && c % k != 0 then
          let ctx ← mkContext ring.type vars
          let h := mkApp7 (mkConst ``Grind.CommRing.eq_norm_unsat_expr) ctx (toExpr l) (toExpr r) (toExpr q) (toExpr (k : Int)) (toExpr c) eagerReflBoolTrue
          let e' ← getFalseExpr
          return .step e' (mkExpectedPropHint h (mkPropEq e e'))
        p := q.addConst (if rel == .eq then c / k else cdiv c k)
        tight? := some (q, k, c)
    -- Nonzero characteristic `c`, `lhsOnly`: when `p` is `k * m + k'` or `k * m₁ - k * m₂` and
    -- `k` has an inverse modulo `c`, multiply by it, so that the equation is solved for `m`
    -- below. `scale?` records `k` and its inverse for the certificate.
    let mut scale? : Option (Int × Int) := none
    if lhsOnly && rel == .eq && kind.isComm && ainvs.isEmpty && !numOrAtom then
      if let some (_, c) := char? then
        if let some k := solvableCoeff? c p then
          if k != 1 then
            if let some k' := modInv? k c then
              p := p.mulConstC k' c
              scale? := some (k, k')
    -- Like `simp +arith`, the equations `x - y = 0` and `x + k = 0` are written `x = y` and
    -- `x = -k`, and any other equation already of the form `p = 0` is left alone.
    let (lp, rp) ←
      if numOrAtom then
        pure (pl, pr)
      else if lhsOnly then
        match rel, char?, p with
        | .eq, none, .add 1 m₁ (.add (-1) m₂ (.num 0)) => pure (.add 1 m₁ (.num 0), .add 1 m₂ (.num 0))
        | .eq, none, .add (-1) m₂ (.add 1 m₁ (.num 0)) => pure (.add 1 m₁ (.num 0), .add 1 m₂ (.num 0))
        | .eq, none, .add 1 m (.num k) => pure (.add 1 m (.num 0), .num (-k))
        | .eq, some (_, c), .add 1 m₁ (.add k m₂ (.num 0)) =>
          pure <| if k + 1 == c then (.add 1 m₁ (.num 0), .add 1 m₂ (.num 0)) else (p, .num 0)
        | .eq, some (_, c), .add 1 m (.num k) => pure (.add 1 m (.num 0), .num ((c - k) % c))
        | _, _, _ =>
          if rel == .eq && char?.isNone && r == .num 0 && p.toExpr == l then return .normal
          pure (p, .num 0)
      else
        let (lp, rp, c) := splitPoly (char?.map (·.2)) p
        pure (if c > 0 then lp.addConst c else lp, if c < 0 then rp.addConst (-c) else rp)
    let l' := lp.toExpr
    let r' := rp.toExpr
    -- A numeral side of a kept `x = k`: a numeral written as such keeps its canonical form, since a
    -- rendered one would use the structure's type as written (`BitVec (id 32)`, `Fin (4 + 1)`)
    -- and be a second literal node; an evaluated one (`2 * 3 - 7`) is rendered.
    let side (p : Poly) (re : RingExpr) (ex : Expr) (ep : RingExpr) : NormM Expr :=
      if numOrAtom && p matches .num _ && re matches .num _ then canonExpr ex
      else denoteRingExpr' vars ep
    let e' ← share (mkApp2 relFn (← side lp l lhs l') (← side rp r rhs r'))
    if isSameExpr e' e then return .normal
    let ctx ← mkContext ring.type vars
    let hoka ← if ainvs.isEmpty then pure (mkConst ``True.intro) else pure (mkInvAtomsOk (← getCommRing) ctx vars ainvs)
    let ainvsE := toExpr ainvsL
    let h ← if let some (q, k, c) := tight? then
      pure <| match rel with
        | .eq => mkApp7 (mkConst ``Grind.CommRing.eq_norm_div_expr) ctx (toExpr l) (toExpr r) (toExpr l') (toExpr r') (toExpr k) eagerReflBoolTrue
        | _ => mkApp9 (mkConst ``Grind.CommRing.le_norm_tight_expr) ctx (toExpr l) (toExpr r) (toExpr l') (toExpr r') (toExpr q) (toExpr k) (toExpr c) eagerReflBoolTrue
    else if let some (k, k') := scale? then
      let (charInst, c) := char?.get!
      let h := mkApp4 (mkConst ``Grind.CommRing.eq_norm_mul_exprC [u]) ring.type (toExpr c) inst charInst
      pure (mkApp8 h ctx (toExpr l) (toExpr r) (toExpr l') (toExpr r') (toExpr k) (toExpr k') eagerReflBoolTrue)
    else if invs.isEmpty && ainvs.isEmpty && kind.isComm && char?.isNone && rp matches .num 0 then
      -- `lhs' ⋈ 0`, where `lp` is the polynomial of `lhs - rhs`: both hypotheses of the theorem
      -- are checked by definitional equality.
      let base (name : Name) : Expr := mkApp2 (mkConst name [u]) ring.type inst
      let h := match rel with
        | .eq => base ``Grind.CommRing.eq_norm_poly0
        | .le =>
          let o := order?.get!
          mkApp4 (base ``Grind.CommRing.le_norm_poly0) o.leInst o.ltInst?.get! o.isPreorderInst o.orderedRingInst?.get!
        | .lt =>
          let o := order?.get!
          mkApp5 (base ``Grind.CommRing.lt_norm_poly0) o.leInst o.ltInst?.get! o.lawfulOrderLTInst?.get! o.isPreorderInst o.orderedRingInst?.get!
      let l'E := toExpr l'
      let pE := toExpr lp
      let bal := useBalanced (.sub l r) (pl.length + pr.length)
      pure (mkAppN h #[ctx, toExpr bal, toExpr l, toExpr r, l'E, pE,
        mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Grind.CommRing.Poly) pE,
        mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Grind.CommRing.Expr) l'E])
    else if invs.isEmpty && ainvs.isEmpty && kind.isComm then
      -- `q` is the polynomial of `lhs - rhs` (`rhs - lhs` for `≤`, `<`); every hypothesis of the
      -- theorem is checked by definitional equality.
      let q := match rel, char? with
        | .eq, none => lp.combine (rp.mulConst (-1))
        | .eq, some (_, c) => lp.combineC (rp.mulConstC (-1) c) c
        | _, none => rp.combine (lp.mulConst (-1))
        | _, some (_, c) => rp.combineC (lp.mulConstC (-1) c) c
      let name := match rel, char? with
        | .eq, none => ``Grind.CommRing.eq_norm_poly
        | .eq, some _ => ``Grind.CommRing.eq_norm_polyC
        | .le, none => ``Grind.CommRing.le_norm_poly
        | .le, some _ => ``Grind.CommRing.le_norm_polyC
        | .lt, none => ``Grind.CommRing.lt_norm_poly
        | .lt, some _ => ``Grind.CommRing.lt_norm_polyC
      let base := match char? with
        | none => mkApp2 (mkConst name [u]) ring.type inst
        | some (charInst, c) => mkApp4 (mkConst name [u]) ring.type (toExpr c) inst charInst
      let h := match rel with
        | .eq => base
        | .le =>
          let o := order?.get!
          mkApp4 base o.leInst o.ltInst?.get! o.isPreorderInst o.orderedRingInst?.get!
        | .lt =>
          let o := order?.get!
          mkApp5 base o.leInst o.ltInst?.get! o.lawfulOrderLTInst?.get! o.isPreorderInst o.orderedRingInst?.get!
      let l'E := toExpr l'
      let r'E := toExpr r'
      let qE := toExpr q
      let reflP := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Grind.CommRing.Poly) qE
      let reflE (e : Expr) := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Grind.CommRing.Expr) e
      let args := #[toExpr l, toExpr r, l'E, r'E, qE, toExpr lp, toExpr rp, reflP, reflE l'E, reflE r'E, reflP]
      pure (mkAppN h (#[ctx, toExpr (useBalanced (.sub l r) (pl.length + pr.length))] ++ args))
    else if invs.isEmpty && ainvs.isEmpty then
      -- `thm type [c] inst [charInst]`, then the order instances.
      let base (name : Name) : Expr :=
        match char? with
        | none => mkApp2 (mkConst name [u]) ring.type inst
        | some (charInst, c) => mkApp4 (mkConst name [u]) ring.type (toExpr c) inst charInst
      let h := match rel with
        | .eq => base (relThmName rel kind.isComm char?.isSome)
        | .le =>
          let o := order?.get!
          mkApp4 (base (relThmName rel kind.isComm char?.isSome)) o.leInst o.ltInst?.get! o.isPreorderInst o.orderedRingInst?.get!
        | .lt =>
          let o := order?.get!
          mkApp5 (base (relThmName rel kind.isComm char?.isSome)) o.leInst o.ltInst?.get! o.lawfulOrderLTInst?.get! o.isPreorderInst o.orderedRingInst?.get!
      pure (mkApp6 h ctx (toExpr l) (toExpr r) (toExpr l') (toExpr r') eagerReflBoolTrue)
    else if invs.isEmpty then
      let base (name : Name) : Expr := mkApp2 (mkConst name [u]) ring.type inst
      let h := match rel with
        | .eq => base ``Grind.CommRing.eq_normA_expr
        | .le =>
          let o := order?.get!
          mkApp4 (base ``Grind.CommRing.le_normA_expr) o.leInst o.ltInst?.get! o.isPreorderInst o.orderedRingInst?.get!
        | .lt =>
          let o := order?.get!
          mkApp5 (base ``Grind.CommRing.lt_normA_expr) o.leInst o.ltInst?.get! o.lawfulOrderLTInst?.get! o.isPreorderInst o.orderedRingInst?.get!
      pure (mkApp8 h ctx ainvsE hoka (toExpr l) (toExpr r) (toExpr l') (toExpr r') eagerReflBoolTrue)
    else
      let (fieldInst, charInst) := fc?.get!
      let base (name : Name) : Expr := mkApp3 (mkConst name [u]) ring.type fieldInst charInst
      let h := match rel with
        | .eq => base ``Grind.CommRing.eq_normQ_expr
        | .le =>
          let o := order?.get!
          mkApp5 (base ``Grind.CommRing.le_normQ_expr) o.leInst o.ltInst?.get! o.lawfulOrderLTInst?.get! linInst?.get! o.orderedRingInst?.get!
        | .lt =>
          let o := order?.get!
          mkApp5 (base ``Grind.CommRing.lt_normQ_expr) o.leInst o.ltInst?.get! o.lawfulOrderLTInst?.get! linInst?.get! o.orderedRingInst?.get!
      let invsE := toExpr invs.toList
      pure (mkAppN h #[ctx, toExpr (useBalanced (.sub l r) (pl.length + pr.length)), invsE,
        mkInvVarsOk ring.type u ctx invsE, ainvsE, hoka, toExpr l, toExpr r, toExpr l', toExpr r', eagerReflBoolTrue])
    return .step e' (mkExpectedPropHint h (mkPropEq e e'))
  else
    let sr ← getSemiring
    let u := sr.u
    -- Instance for `eq_normS` / `eq_normS_nc`: `CommSemiring` or `Semiring`.
    let (inst, normS) ← if kind.isComm then
        pure ((← getCommSemiring).commSemiringInst, ``Grind.CommRing.eq_normS)
      else
        pure (sr.semiringInst, ``Grind.CommRing.eq_normS_nc)
    -- Cancellation needs `AddRightCancel` for `=` and the ordered structure for `≤`/`<`.
    let cancel? : Option (Expr → Expr → Expr → Expr) ← match rel with
      | .eq =>
        let some addInst ← MonadCanon.synthInstance? (mkApp (mkConst ``Add [u]) sr.type) | pure none
        let arcInst? ← if kind.isComm then getAddRightCancelInst?
          else MonadCanon.synthInstance? (mkApp2 (mkConst ``Grind.AddRightCancel [u]) sr.type addInst)
        match arcInst? with
        | none => pure none
        | some arcInst =>
          pure <| some fun a b c => mkApp6 (mkConst ``Grind.AddRightCancel.add_right_cancel_iff [u]) sr.type addInst arcInst a b c
      | .le | .lt =>
        let o := order?.get!
        let hAdd := mkApp2 (mkConst ``instHAdd [u]) sr.type (mkApp2 (mkConst ``Grind.Semiring.toAdd [u]) sr.type sr.semiringInst)
        let addFn := mkApp4 (mkConst ``HAdd.hAdd [u, u, u]) sr.type sr.type sr.type hAdd
        let ordAdd := mkApp6 (mkConst ``Grind.OrderedRing.toOrderedAdd [u]) sr.type sr.semiringInst o.leInst o.ltInst?.get! o.isPreorderInst o.orderedRingInst?.get!
        if rel == .le then
          pure <| some fun a b c =>
            let iff := mkApp8 (mkConst ``Grind.OrderedAdd.add_le_left_iff [u]) sr.type hAdd o.leInst o.isPreorderInst ordAdd a b c
            mkIffSymm (mkApp2 o.leFn a b) (mkApp2 o.leFn (mkApp2 addFn a c) (mkApp2 addFn b c)) iff
        else
          let acm := mkApp2 (mkConst ``Grind.NatModule.toAddCommMonoid [u]) sr.type (mkApp2 (mkConst ``Grind.Semiring.toNatModule [u]) sr.type sr.semiringInst)
          let ltFn := o.ltFn?.get!
          pure <| some fun a b c =>
            let iff := mkApp10 (mkConst ``Grind.OrderedAdd.add_lt_left_iff [u]) sr.type o.leInst o.isPreorderInst acm ordAdd o.ltInst?.get! o.lawfulOrderLTInst?.get! a b c
            mkIffSymm (mkApp2 ltFn a b) (mkApp2 ltFn (mkApp2 addFn a c) (mkApp2 addFn b c)) iff
    let c := commonPart pl pr
    let hasC := cancel?.isSome && !c.isZero
    let (lp, rp) := if hasC then (pl.combine (c.mulConst (-1)), pr.combine (c.mulConst (-1))) else (pl, pr)
    let l' := lp.toExpr
    let r' := rp.toExpr
    let el ← share (← denoteSemiringExpr' vars l')
    let er ← share (← denoteSemiringExpr' vars r')
    let e' ← share (mkApp2 relFn el er)
    if isSameExpr e' e then return .normal
    let ctx ← mkContext sr.type vars
    -- Term steps `lhs = lhs' + c` and `rhs = rhs' + c` (without `+ c` when nothing is cancelled).
    -- `px` is the polynomial of `x` and `qx` the one of the rendered `x'`. In a commutative
    -- semiring the polynomials are checked by definitional equality and only `x` is normalized.
    let cE := toExpr c
    let reflP (p : Expr) := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Grind.CommRing.Poly) p
    let reflE (e : Expr) := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Grind.CommRing.Expr) e
    let mkTermStep (x xC : RingExpr) (px qx : Poly) (ex exC : Expr) : Expr :=
      let xE := toExpr x
      let xCE := toExpr xC
      let h := if !kind.isComm then
          mkApp6 (mkConst normS [u]) sr.type inst ctx xE xCE eagerReflBoolTrue
        else if hasC then
          let pxE := toExpr px
          let thm := mkApp2 (mkConst ``Grind.CommRing.Expr.eq_of_toPolyS_eq_add_toExpr [u]) sr.type inst
          mkAppN thm #[ctx, toExpr (useBalanced x px.length), xE, xCE, pxE, toExpr qx, cE, reflP pxE, reflE xCE, reflP pxE, eagerReflBoolTrue]
        else
          let pxE := toExpr px
          let thm := mkApp2 (mkConst ``Grind.CommRing.Expr.eq_of_toPolyS_eq_toExpr [u]) sr.type inst
          mkApp7 thm ctx (toExpr (useBalanced x px.length)) xE xCE pxE (reflP pxE) (reflE xCE)
      mkExpectedPropHint h (mkApp3 (mkConst ``Eq [u.succ]) sr.type ex exC)
    let (lC, rC) : RingExpr × RingExpr := if hasC then (.add l' c.toExpr, .add r' c.toExpr) else (l', r')
    let elC ← if hasC then share (← denoteSemiringExpr' vars lC) else pure el
    let erC ← if hasC then share (← denoteSemiringExpr' vars rC) else pure er
    let r₁ : Result := if isSameExpr lhs elC then .rfl else .step elC (mkTermStep l lC pl lp lhs elC)
    let r₂ : Result := if isSameExpr rhs erC then .rfl else .step erC (mkTermStep r rC pr rp rhs erC)
    let eR ← mkAppS₂ relFn lhs rhs
    let rel₁ ← match h : eR with
      | .app fa@h':(.app f a) b => congrBin eR fa f a b r₁ r₂ h h'
      | _ => unreachable!
    let eC := rel₁.getResultExpr e
    if !hasC then
      match rel₁ with
      | .rfl .. => return .normal
      | .step _ h .. => return .step e' h
    let some mkIff := cancel? | throwError "internal error: `Sym.Arith` relation normalizer has no cancellation lemma"
    let ec ← share (← denoteSemiringExpr' vars c.toExpr)
    let hCancel := mkExpectedPropHint (mkPropExt eC e' (mkIff el er ec)) (mkPropEq eC e')
    match rel₁ with
    | .rfl .. => return .step e' hCancel
    | .step _ h .. => return .step e' (← Simp.mkEqTrans e eC h e' hCancel)

/--
The `NormM` part of `normalizeDvd?`: `e₁` is `k ∣ arg` with the atoms of `arg` simplified, `x`
the reification of `arg` with its polynomial `p` over the compact variables `vars`.
-/
private def normalizeDvdCore (e₁ dvdFn : Expr) (k : Int) (x : RingExpr) (p : Poly) (vars : Array Expr) : NormM CoreResult := do
  let ring ← getRing
  let g : Nat := Nat.gcd k.natAbs (gcdMonCoeffs p)
  let c := polyConst p
  let q := divMonCoeffs g p
  let ctx ← mkContext ring.type vars
  if c % g != 0 then
    let h := mkApp7 (mkConst ``Grind.CommRing.dvd_norm_unsat_expr) ctx (toExpr k) (toExpr x) (toExpr q) (toExpr (g : Int)) (toExpr c) eagerReflBoolTrue
    let e' ← getFalseExpr
    return .step e' (mkExpectedPropHint h (mkPropEq e₁ e'))
  let k' := k / g
  let x' := (q.addConst (c / g)).toExpr
  let e' ← share (mkApp2 dvdFn (mkIntLit k') (← denoteRingExpr' vars x'))
  if isSameExpr e' e₁ then return .normal
  let h := mkApp9 (mkConst ``Grind.CommRing.dvd_norm_expr) ctx (toExpr k) (toExpr x) (toExpr x') (toExpr k') (toExpr q) (toExpr (g : Int)) (toExpr c) eagerReflBoolTrue
  return .step e' (mkExpectedPropHint h (mkPropEq e₁ e'))

/-! ## Entry points -/

section Entry
variable [Monad m] [MonadLiftT SymM m] [MonadLiftT MetaM m]

/-- Runs a `NormM` computation for the structure `kind`, outside a visit. -/
private def runNormM (kind : Kind) (x : NormM α) : m α :=
  (x.run { kind }).run' {}

/-- Runs the visit `k` for the structure `kind` with a fresh variable array. -/
private def runNorm (kind : Kind) (distrib : Bool) (k : VisitM m α) : m α := do
  let (polyCfg, charZero) ← runNormM kind do pure (← polyConfig, (← fieldChar0?).isSome)
  (k.run { kind, distrib, polyCfg, charZero }).run' {}

/--
`true` if the structure `kind` has a characteristic the normalizer must leave alone: a numeral
above `maxChar?`, or one that is not a numeral (`BitVec w`, `Fin n`). See `normalize?`.
-/
private def charAboveLimit (kind : Kind) (maxChar? : Option Nat) : m Bool := do
  let some maxChar := maxChar? | return false
  let s ← (getArithState : SymM _)
  let (charInst?, symbolicChar) := match kind with
    | .commRing id => let r := s.rings[id]!; (r.charInst?, r.symbolicChar)
    | .commSemiring id => let r := s.rings[s.semirings[id]!.ringId]!; (r.charInst?, r.symbolicChar)
    | .ring id => let r := s.ncRings[id]!; (r.charInst?, r.symbolicChar)
    | .semiring id => let r := s.ncSemirings[id]!; (r.charInst?, r.symbolicChar)
  if symbolicChar then return true
  let some (_, c) := charInst? | return false
  return c > maxChar

/-- The kind of the structure of `α`, if the normalizer supports it. -/
private def classifyKind? (α : Expr) : m (Option Kind) := do
  return match (← classify? α) with
    | .commRing id => some (.commRing id)
    | .commSemiring id => some (.commSemiring id)
    | .nonCommRing id => some (.ring id)
    | .nonCommSemiring id => some (.semiring id)
    | .none => none

/-- The `normalize?` path for relations; `e` is `rel lhs rhs` with carrier `α`. -/
private def normalizeRel? (v : Visitor m) (rel : RelKind) (α e lhs rhs : Expr) (lhsOnly distrib : Bool) (maxChar? : Option Nat) : m Result := do
  let some kind ← classifyKind? α | return .rfl
  if (← charAboveLimit kind maxChar?) then return .rfl
  let order? ← match rel with
    | .eq => pure none
    | .le | .lt =>
      let some id ← classifyOrder? α | return .rfl
      let o := (← getArithState).orders[id]!
      unless o.orderedRingInst?.isSome do return .rfl
      if rel == .lt then unless o.lawfulOrderLTInst?.isSome do return .rfl
      -- The relation's instance must be the classified one; compare the canonicalized prefix.
      let fn := if rel == .le then o.leFn else o.ltFn?.get!
      let ok ← runNormM kind do return isSameExpr fn (← canonExpr e.appFn!.appFn!)
      unless ok do return .rfl
      pure (some o)
  runNorm kind distrib do
    let nl ← visit v lhs
    let nr ← visit v rhs
    let r₀ ← match h : e with
      | .app fa@h':(.app f a) b => congrBin e fa f a b nl.r nr.r h h'
      | _ => unreachable!
    let e₁ := r₀.getResultExpr e
    let lhs₁ := e₁.appFn!.appArg!
    let rhs₁ := e₁.appArg!
    let relFn := match rel, order? with
      | .eq, _ => e₁.appFn!.appFn!
      | .le, some o => o.leFn
      | .lt, some o => o.ltFn?.get!
      | _, none => e₁.appFn!.appFn!
    -- In a field, the inverse pairs are those of `lhs - rhs`.
    let (ainvs, cd) ← if (← liftNorm (isFieldKind kind)) then
        match (← runPoly (do SafePoly.combine nl.p (← SafePoly.mulConst (-1) nr.p) : PolyM Poly)) with
        | some pd => decideInvAtoms v pd
        | none => pure (#[], false)
      else pure (#[], false)
    let r ← liftNorm do
      let (f, vars) ← compactVars (.add nl.re nr.re)
      let ainvs := ainvs.map fun (y, x, h) => (f y, f x, h)
      let comm := (← read).polyCfg.commutative
      normalizeRelCore rel relFn order? e₁ lhs₁ rhs₁ (nl.re.renameVars f) (nr.re.renameVars f)
        (renamePoly nl.p f comm) (renamePoly nr.p f comm) vars ainvs lhsOnly
    match r with
    | .notApplicable => return if cd then r₀.withContextDependent else r₀
    | .normal => return if cd then r₀.markAsDone.withContextDependent else r₀.markAsDone
    | .step e' h₂ =>
      match r₀ with
      | .rfl _ cd₀ => return .step e' h₂ (done := true) (contextDependent := cd₀ || cd)
      | .step _ h₁ _ cd₀ => mkEqTransResult e e₁ h₁ (.step e' h₂ (done := true) (contextDependent := cd)) cd₀

/--
Normalizes the arithmetic term `e` (an application of `+`, `-`, `*`, `^`, `•`, negation, or,
in a field, `/` and `⁻¹`, whose carrier type is a ring or semiring) into polynomial normal
form, after simplifying its atoms with `simpAtom`. `e` must be maximally shared.

The result distinguishes three cases:
* `.rfl`: the normalizer does not apply (`e` is not such a term, or it is an atom for its
  structure, or the polynomial exceeds the `sym.arith.maxTerms`/`sym.arith.maxDegree` budget
  or the exponent threshold, in which case an issue is reported). If `simpAtom` rewrote atoms,
  the result is that rewrite instead, with `done := false`, so that a simplifier still visits
  the subterms.
* `.rfl (done := true)` (or the atom rewrite marked `done`): `e` is already in normal form.
* `.step e' h (done := true)`: `e` normalizes to `e'`.

`discharge?` proves the side conditions `x ≠ 0` that cancel `x * x⁻¹` in a field; a result
that asked for one is `contextDependent`. `distrib` is described at `normalize?`.
-/
private def normalizeTerm? (v : Visitor m) (e : Expr) (distrib : Bool) (maxChar? : Option Nat) : m Result := do
  let some α := getArithType? e | return .rfl
  let some kind ← classifyKind? α | return .rfl
  if (← charAboveLimit kind maxChar?) then
    -- A cast of a numeral still becomes the numeral of the carrier, so that a numeral has one
    -- representation; everything else is left as written.
    let some (e₂, h) ← runNormM kind (mkCastLitStep? kind e) | return .rfl
    return .step e₂ h (done := true)
  let isRing := kind.isRing
  let isField ← isFieldKind kind
  -- Roots that the structure does not interpret are atoms.
  match_expr e with
  | HPow.hPow _ _ _ _ _ k => unless (Sym.getNatValue? k).run.isSome do return .rfl
  | HSub.hSub _ _ _ _ _ _ => unless isRing do return .rfl
  | Neg.neg _ _ _ => unless isRing do return .rfl
  | HDiv.hDiv _ _ _ _ _ _ => unless isField do return .rfl
  | Inv.inv _ _ _ => unless isField do return .rfl
  | IntCast.intCast _ _ _ => unless isRing do return .rfl
  | _ => pure ()
  runNorm kind distrib do
    let n ← visit v e
    normalizeNode v e n

/--
The `normalize?` path for `k ∣ arg` over `Int` with a numeral `k ≠ 0`; `dvdFn` is
`Dvd.dvd Int inst`. Like `simp +arith`, the constraint is divided by the gcd `g` of `k` and
the coefficients of `arg`: `k ∣ g * q + c` becomes `False` when `g ∤ c`, and `k / g ∣ q + c / g`
otherwise (`IntSolver.lean`).
-/
private def normalizeDvd? (v : Visitor m) (e dvdFn arg : Expr) (k : Int) (distrib : Bool) (maxChar? : Option Nat) : m Result := do
  let some kind@(.commRing _) ← classifyKind? dvdFn.appFn!.appArg! | return .rfl
  if (← charAboveLimit kind maxChar?) then return .rfl
  runNorm kind distrib do
    let n ← visit v arg
    let r₀ ← match h : e with
      | .app f a => Simp.mkCongrArg e f a n.r h
      | _ => unreachable!
    let e₁ := r₀.getResultExpr e
    let r ← liftNorm do
      let (f, vars) ← compactVars n.re
      normalizeDvdCore e₁ dvdFn k (n.re.renameVars f) (renamePoly n.p f (← read).polyCfg.commutative) vars
    match r with
    | .notApplicable => return r₀
    | .normal => return r₀.markAsDone
    | .step e' h₂ =>
      match r₀ with
      | .rfl _ cd₀ => return .step e' h₂ (done := true) (contextDependent := cd₀)
      | .step _ h₁ _ cd₀ => mkEqTransResult e e₁ h₁ (.step e' h₂ (done := true)) cd₀

/--
The `NormM` part of `cancelNatSub?`, for the visited sides `a` and `b`: the steps `a = a' + c` and
`b = b' + c` and the terms `a'`, `b'`, `c`, or `none` when the common part `c` is zero.
-/
private def cancelNatSubCore (a b : Expr) (na nb : Node) : NormM (Option (Result × Result × Expr × Expr × Expr)) := do
  let (f, vars) ← compactVars (.add na.re nb.re)
  let pa := renamePoly na.p f true
  let pb := renamePoly nb.p f true
  let c := commonPart pa pb
  if c.isZero then return none
  let a' := (pa.combine (c.mulConst (-1))).toExpr
  let b' := (pb.combine (c.mulConst (-1))).toExpr
  let sr ← getCommSemiring
  let ctx ← mkContext sr.type vars
  let denote (x : RingExpr) : NormM Expr := do share (← denoteSemiringExpr' vars x)
  -- `x = x' + c`, chained after the node's own step `x = x₁`.
  let termStep (x : Expr) (n : Node) (x' : RingExpr) : NormM Result := do
    let x₁ := n.r.getResultExpr x
    let xC : RingExpr := .add x' c.toExpr
    let ex ← denote xC
    if isSameExpr x₁ ex then return n.r
    let h := mkExpectedPropHint
      (mkApp6 (mkConst ``Grind.CommRing.eq_normS [sr.u]) sr.type sr.commSemiringInst ctx (toExpr (n.re.renameVars f)) (toExpr xC) eagerReflBoolTrue)
      (mkApp3 (mkConst ``Eq [sr.u.succ]) sr.type x₁ ex)
    chainResults x x₁ n.r (.step ex h)
  return some (← termStep a na a', ← termStep b nb b', ← denote a', ← denote b', ← denote c.toExpr)

/-- `e₁ := (a' + c) - (b' + c) = a' - b'`, by `Nat.add_sub_add_right`. -/
private def mkNatSubCancelStep (subFn e₁ a' b' c : Expr) : NormM (Expr × Expr) := do
  let e' ← mkAppS₂ subFn a' b'
  let h := mkApp3 (mkConst ``Nat.add_sub_add_right) a' c b'
  return (e', mkExpectedPropHint h (mkNatEq e₁ e'))

/--
Cancels the common part of the sides of the `Nat` subtraction `e := a - b`, an atom of the `Nat`
semiring: with `a` and `b` normalized to `a' + c` and `b' + c`, where `c` is the monomial-wise
minimum of their polynomials, `e` becomes `a' - b'` (`Nat.add_sub_add_right`). So `x + 2 - 1`
is `x + 1 - 0` and `x * y + 3 - (x * y + z + 1)` is `2 - z`; `a' - 0` and `0 - b'` are left
to the caller. Returns `.rfl` when `c` is zero. The result is not `done`. `simpAtom` and
`distrib` are as in `normalize?`.
-/
def cancelNatSub? (e : Expr) (simpAtom : Expr → m Result) (distrib : Bool := true) : m Result := do
  let_expr HSub.hSub α β γ inst a b := e | return .rfl
  -- Distinct atoms have nothing in common, and `x - x` is left to `Nat.sub_self`.
  unless isInterpreted a || isInterpreted b do return .rfl
  unless α.isConstOf ``Nat && β.isConstOf ``Nat && γ.isConstOf ``Nat do return .rfl
  unless (← Structural.isInstHSubNat inst) do return .rfl
  let some kind@(.commSemiring _) ← classifyKind? α | return .rfl
  let v : Visitor m := { simpAtom, discharge? := fun _ => pure none }
  runNorm kind distrib do
    match h : e with
    | .app fa@h':(.app subFn a) b =>
      let na ← visit v a
      let nb ← visit v b
      let some (ra, rb, ea', eb', ec) ← liftNorm (cancelNatSubCore a b na nb) | return .rfl
      let r₀ ← congrBin e fa subFn a b ra rb h h'
      let e₁ := r₀.getResultExpr e
      let (e', h) ← liftNorm (mkNatSubCancelStep subFn e₁ ea' eb' ec)
      chainResults e e₁ r₀ (.step e' h)
    | _ => unreachable!

end Entry

/--
Normalizes `e` into polynomial normal form after simplifying its atoms with `simpAtom`:
either an arithmetic term (see `normalizeTerm?`), a relation `lhs = rhs`, `lhs ≤ rhs`,
`lhs < rhs` whose carrier type is a `CommRing` or `CommSemiring` (see "Relations"), or an
`Int` divisibility constraint `k ∣ e` with a numeral `k` (see `normalizeDvd?`).
`e` must be maximally shared. The result cases are those of `normalizeTerm?`. A normalized
relation is `done` as well; a simplifier that wants `post` to see normalized relations (to
close `t = t`, say) must apply it itself, as `Sym.Simp.simpArith` does.

`discharge?` is asked for the side conditions `x ≠ 0` under which `x * x⁻¹` is cancelled in a
field; by default none is proved.

With `lhsOnly := true`, a relation over a ring is normalized to `p = 0`, `p ≤ 0`, or `p < 0`
with `p` the polynomial of `lhs - rhs`, instead of being split by sign (see "Relations"); the
exceptions follow `simp +arith`: equations between atoms and numerals (`x = y`, `x = 3`,
`3 = x`) and equations already of the form `p = 0` are left alone, and `x - y = 0` and
`x + k = 0` are written `x = y` and `x = -k`. This is the normal form of the `grind`
normalizer. Semirings have no subtraction and are unaffected.

With `distrib := false`, multiplication is not distributed over addition: a product is
expanded only when one factor is a scalar (a constant, or a numeral inverse in a field of
characteristic zero) or both are monomials, a power only when its base is a monomial, and in a
field `(a * b)⁻¹` and `(a ^ n)⁻¹` are not rewritten. Any other product, power, or inverse is an
atom whose factors are normalized separately, so `x * (y + 1)` stays `x * (y + 1)` while
`2 * (y + 1)` becomes `2 * y + 2`. This keeps the nonlinear atoms that decision procedures for
linear arithmetic see, as a simplifier that only linearizes would.

With `maxChar? := some c`, terms over a structure whose characteristic is a numeral above `c`,
or is not a numeral (`BitVec w`, `Fin n`), are left as written; only casts of numerals are still
rewritten to the numeral of the carrier. In such a structure the normal form reduces
coefficients modulo the characteristic, so `x - y` over `BitVec 64` would become
`x + 18446744073709551615 * y`, which hides the subtraction from rewrite rules and from
`grind`'s `[grind hom]` translation. Structures with no `IsCharP` instance are normalized:
without a known characteristic no coefficient is reduced.
-/
def normalize? [Monad m] [MonadLiftT SymM m] [MonadLiftT MetaM m] (e : Expr) (simpAtom : Expr → m Result)
    (discharge? : Expr → m (Option Expr) := fun _ => pure none) (lhsOnly : Bool := false) (distrib : Bool := true)
    (maxChar? : Option Nat := none) : m Result := do
  let v : Visitor m := { simpAtom, discharge? }
  match_expr e with
  | Eq α lhs rhs => normalizeRel? v .eq α e lhs rhs lhsOnly distrib maxChar?
  | LE.le α _ lhs rhs => normalizeRel? v .le α e lhs rhs lhsOnly distrib maxChar?
  | LT.lt α _ lhs rhs => normalizeRel? v .lt α e lhs rhs lhsOnly distrib maxChar?
  | Dvd.dvd α _ k arg =>
    if α.isConstOf ``Int then
      if let some kv := (Sym.getIntValue? k).run then
        if kv != 0 then
          return ← normalizeDvd? v e e.appFn!.appFn! arg kv distrib maxChar?
    normalizeTerm? v e distrib maxChar?
  | _ => normalizeTerm? v e distrib maxChar?

end Lean.Meta.Sym.Arith
