/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Sym.Arith.SafePoly
public import Lean.Meta.Sym.Arith.Reify
public import Lean.Meta.Sym.Arith.DenoteExpr
public import Lean.Meta.Sym.Simp.Result
public import Lean.Meta.Sym.Canon
public import Lean.Meta.Sym.SynthInstance
public import Lean.Meta.Sym.Arith.Classify
public import Lean.Meta.Sym.Arith.VarRename
import Lean.Meta.Sym.Arith.ToExpr
public import Lean.Meta.Sym.Simp.App
import Lean.Meta.AppBuilder
import Lean.Meta.Sym.AlphaShareBuilder
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

The normalizer owns the traversal of the arithmetic tree: it recurses through the operators
its structure interprets and hands every atom (maximal non-arithmetic subterm) to the
`simpAtom` callback, so that a simplifier can rewrite the atoms before reification and the
normal form is stated for the simplified atoms. The congruence proof for that step is built
with `Sym.Simp.mkCongr`. A cast of a numeral (`↑(2 : Nat)`, `↑(-2 : Int)`) is rewritten to the
numeral of the carrier on the way, also when it is the whole term, so that a numeral has one
representation.

Atoms are numbered in `Expr.lt` order, so the normal form of a term does not depend on the
order in which its atoms occur, and two terms denoting the same polynomial over the same
atoms normalize to the same (maximally shared) expression.

The input is not assumed to be canonicalized. Reification runs on a copy of the term whose
operator and cast prefixes (`HAdd.hAdd α α α inst`, `NatCast.natCast α inst`, ...) and numerals
are canonicalized (`canonArith`); the atoms are otherwise shared with the original, the proof is stated for the original term, and the
kernel closes the gap between the goal's instances and the canonical ones of the output
while checking the expected type, as it does for `grind`. The copy is the term itself when
the instances are already canonical.
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
  /-- Inverse atoms whose side condition was discharged: `(x⁻¹, x, h)` with `h : x ≠ 0`. -/
  atomInvs : Array (Expr × Expr × Expr) := #[]

structure NormM.State where
  vars   : Array Expr := #[]
  varMap : PHashMap ExprPtr Var := {}
  /-- Side conditions the caller should discharge: `(x⁻¹, x, x ≠ 0)`, see `getInvAtoms`. -/
  invCands : Array (Expr × Expr × Expr) := #[]

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
  | HAdd.hAdd α _ _ _ _ _ => some α
  | HSub.hSub α _ _ _ _ _ => some α
  | HMul.hMul α _ _ _ _ _ => some α
  | HPow.hPow α β _ _ _ _ => if β.isConstOf ``Nat then some α else none
  | HSMul.hSMul σ α _ _ _ _ => if σ.isConstOf ``Nat || σ.isConstOf ``Int then some α else none
  | Neg.neg α _ _ => some α
  | HDiv.hDiv α _ _ _ _ _ => some α
  | Inv.inv α _ _ => some α
  | NatCast.natCast α _ a => if (Sym.getNatValue? a).run.isSome then some α else none
  | IntCast.intCast α _ a => if (Sym.getIntValue? a).run.isSome then some α else none
  | _ => none

/-- `true` if the structure of `kind` is a field. -/
private def isFieldKind (kind : Kind) : SymM Bool := do
  let .commRing id := kind | return false
  return (← getArithState).rings[id]!.fieldInst?.isSome

/-!
## Simplifying the atoms

`visitAtoms` traverses the arithmetic tree of `e` (the nodes the structure interprets, by head
symbol) and applies `simpAtom` to the atoms, returning the term with simplified atoms and its
congruence proof. Nodes with a non-canonical instance are still traversed here and become
atoms in the reifier; their subterms are simplified either way.
-/

section Visit
variable [Monad m] [MonadLiftT SymM m] [MonadLiftT MetaM m]

private def liftNorm (kind : Kind) (x : NormM α) : m α :=
  ((x.run { kind }).run' {} : SymM α)

/--
Congruence step for `e := f a b`. `fa` is the subterm `f a` of `e`: a rebuilt `.app f a` would be
a fresh node, which is not maximally shared.
-/
private def congrBin (e fa f a b : Expr) (ra rb : Result) (h₁ : e = .app (.app f a) b) (h₂ : fa = .app f a) : m Result := do
  let r ← (Simp.mkCongrArg fa f a ra h₂ : SymM Result)
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
and cancels `x * x⁻¹` under a discharged `x ≠ 0` (`getInvAtoms`).
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

/-- The inverse rewrites, for `e := x⁻¹` with the field's `Inv` instance. -/
private def mkInvStep? (e x : Expr) : NormM (Option (Expr × Expr)) := do
  let ring ← getCommRing
  let fieldInst := ring.fieldInst?.get!
  let invFn ← getInvFn
  let thm (name : Name) : Expr := mkApp2 (mkConst name [ring.u]) ring.type fieldInst
  match_expr x with
  | HMul.hMul _ _ _ _ a b =>
    unless isSameExpr (← getMulFn) (← canonExpr x.appFn!.appFn!) do return none
    return some (← mkFieldStep (mkApp2 (thm ``Grind.Field.inv_mul) a b) e (mkApp2 (← getMulFn) (mkApp invFn a) (mkApp invFn b)))
  | HPow.hPow _ _ _ _ a k =>
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

private partial def visitAtoms (kind : Kind) (isField : Bool) (simpAtom : Expr → m Result) (e : Expr) : m Result := do
  let isRing := kind.isRing
  let bin : m Result := do
    match h : e with
    | .app fa@h':(.app f a) b => congrBin e fa f a b (← visitAtoms kind isField simpAtom a) (← visitAtoms kind isField simpAtom b) h h'
    | _ => unreachable!
  let un : m Result := do
    match h : e with
    | .app f a => (Simp.mkCongrArg e f a (← visitAtoms kind isField simpAtom a) h : SymM Result)
    | _ => unreachable!
  -- A cast of a numeral becomes the numeral of the carrier. With a different cast instance, it is
  -- an atom, but one `simpAtom` must not visit: `simp` would re-enter `e` through `normalizeTerm?`.
  let castLit : m Result := do
    let some (e₂, h) ← liftNorm kind (mkCastLitStep? kind e) | return .rfl
    return .step e₂ h
  match_expr e with
  | HAdd.hAdd _ _ _ _ _ _ => bin
  | HMul.hMul _ _ _ _ _ _ => bin
  | HSub.hSub _ _ _ _ _ _ => if isRing then bin else simpAtom e
  | Neg.neg _ _ _ => if isRing then un else simpAtom e
  | HPow.hPow _ _ _ _ _ k =>
    -- Only literal exponents are interpreted; the exponent is not simplified.
    unless (Sym.getNatValue? k).run.isSome do return (← simpAtom e)
    match h : e with
    | .app fa@h':(.app f a) k => congrBin e fa f a k (← visitAtoms kind isField simpAtom a) .rfl h h'
    | _ => unreachable!
  | HSMul.hSMul σ _ _ _ _ _ =>
    let isNat := σ.isConstOf ``Nat
    unless isNat || (isRing && σ.isConstOf ``Int) do return (← simpAtom e)
    -- The instance must be the structure's `nsmul`/`zsmul`; compare the canonicalized prefix.
    let ok ← liftNorm kind do
      let fn ← match kind.isRing, isNat with
        | true, true => getNatSMulFn
        | true, false => getIntSMulFn
        | false, _ => getNatSMulFn'
      return isSameExpr fn (← canonExpr e.appFn!.appFn!)
    unless ok do return (← simpAtom e)
    match h : e with
    | .app fk@h':(.app f k) a =>
      let r₁ ← congrBin e fk f k a (← simpAtom k) (← visitAtoms kind isField simpAtom a) h h'
      let e₁ := r₁.getResultExpr e
      let (e₂, h₂) ← liftNorm kind (mkSMulStep kind isNat e₁ e₁.appFn!.appArg! e₁.appArg!)
      match r₁ with
      | .rfl _ cd => return .step e₂ h₂ (contextDependent := cd)
      | .step _ h₁ _ cd => mkEqTransResult e e₁ h₁ (.step e₂ h₂) cd
    | _ => unreachable!
  | HDiv.hDiv _ _ _ _ a b =>
    unless isField do return (← simpAtom e)
    let ok ← liftNorm kind do return isSameExpr (← getDivFn) (← canonExpr e.appFn!.appFn!)
    unless ok do return (← simpAtom e)
    let (e₂, h) ← liftNorm kind (mkDivStep e a b)
    mkEqTransResult e e₂ h (← visitAtoms kind isField simpAtom e₂)
  | Inv.inv _ _ _ =>
    unless isField do return (← simpAtom e)
    let ok ← liftNorm kind do return isSameExpr (← getInvFn) (← canonExpr e.appFn!)
    unless ok do return (← simpAtom e)
    -- Simplify `x` (a proper subterm, so `simp` normalizes it without re-entering `e`),
    -- then rewrite `x'⁻¹`.
    match h : e with
    | .app f x =>
      let r ← (Simp.mkCongrArg e f x (← simpAtom x) h : SymM Result)
      let e₁ := r.getResultExpr e
      let some (e₂, h₁) ← liftNorm kind (mkInvStep? e₁ e₁.appArg!) | return r
      let r₂ ← visitAtoms kind isField simpAtom e₂
      let r₁ ← mkEqTransResult e₁ e₂ h₁ r₂
      match r with
      | .rfl _ cd => return if cd && !r₁.isContextDependent then r₁.withContextDependent else r₁
      | .step _ h₀ _ cd => mkEqTransResult e e₁ h₀ r₁ cd
    | _ => unreachable!
  | NatCast.natCast _ _ a =>
    unless (Sym.getNatValue? a).run.isSome do return (← simpAtom e)
    castLit
  | IntCast.intCast _ _ a =>
    unless isRing && (Sym.getIntValue? a).run.isSome do return (← simpAtom e)
    castLit
  | OfNat.ofNat _ _ _ => return .rfl
  | _ => simpAtom e

end Visit

/--
Canonicalizes the operator prefixes, the numerals, and the cast prefixes of the arithmetic tree
rooted at `e`, without touching the atoms otherwise, so that the reifier's pointer checks against
the cached operators succeed. Nodes that the structure does not interpret (`-` in a semiring,
`^` with a symbolic exponent, casts of non-literals) are atoms. Returns `e` itself when nothing
changes.
-/
private partial def canonArith (e : Expr) : NormM Expr := do
  let isRing := (← getKind).isRing
  let bin (e a b : Expr) : NormM Expr := do
    let f := e.appFn!.appFn!
    let f' ← canonExpr f
    let a' ← canonArith a
    let b' ← canonArith b
    if isSameExpr f f' && isSameExpr a a' && isSameExpr b b' then return e
    mkAppS₂ f' a' b'
  let un (e a : Expr) : NormM Expr := do
    let f := e.appFn!
    let f' ← canonExpr f
    let a' ← canonArith a
    if isSameExpr f f' && isSameExpr a a' then return e
    mkAppS f' a'
  let castLit (e a : Expr) : NormM Expr := do
    let f := e.appFn!
    let f' ← canonExpr f
    if isSameExpr f f' then return e
    mkAppS f' a
  match_expr e with
  | HAdd.hAdd _ _ _ _ a b => bin e a b
  | HMul.hMul _ _ _ _ a b => bin e a b
  | HSub.hSub _ _ _ _ a b => if isRing then bin e a b else return e
  | Neg.neg _ _ a => if isRing then un e a else return e
  | HPow.hPow _ _ _ _ a k =>
    unless (Sym.getNatValue? k).run.isSome do return e
    let f := e.appFn!.appFn!
    let f' ← canonExpr f
    let a' ← canonArith a
    if isSameExpr f f' && isSameExpr a a' then return e
    mkAppS₂ f' a' k
  -- Casts are canonicalized for every argument: a cast of a non-literal is an atom, and a
  -- noncanonical instance (e.g. `Semiring.natCast` from a generic rewrite rule) would otherwise
  -- make `↑a` a different atom from the canonical `↑a`.
  | NatCast.natCast _ _ a => castLit e a
  | IntCast.intCast _ _ a => if isRing then castLit e a else return e
  | OfNat.ofNat _ _ _ => canonExpr e
  | _ => return e

/-! ## Reflection -/

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
The inverse pairs among the atoms: `(y, x, h)` for `vars[y] = vars[x]⁻¹` with the field's `Inv`
instance, `h : vars[x] ≠ 0`, and some monomial of `p` containing both. The side conditions
come from `atomInvs`. When none was decided yet, the pairs are recorded in `invCands` with
their side condition instead, and the normalization proceeds without cancellation; `runCore`
reruns it with the discharged ones.
-/
private def getInvAtoms (vars : Array Expr) (p : Poly) : NormM (Array (Var × Var × Expr)) := do
  let invFn ← getInvFn
  let decided := (← read).atomInvs
  let mut result := #[]
  for (e, y) in vars.zipIdx do
    let_expr Inv.inv _ _ n := e | continue
    unless isSameExpr invFn (← canonExpr e.appFn!) do continue
    let some x := vars.findIdx? (isSameExpr · n) | continue
    unless sharesMonomial p x y do continue
    if let some (_, _, h) := decided.find? fun (inv, _, _) => isSameExpr inv e then
      result := result.push (y, x, h)
    else if decided.isEmpty then
      let ring ← getRing
      let prop := mkApp3 (mkConst ``Ne [ring.u.succ]) ring.type n (← denoteNum 0)
      modify fun s => { s with invCands := s.invCands.push (e, n, prop) }
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
  /-- See `normalizeCore`. -/
  | notApplicable
  /-- The term is already in normal form. -/
  | normal
  /-- The term normalizes to `e'` with proof `h`. -/
  | step (e' h : Expr)

private def mkContext (type : Expr) (zero : Expr) (vars : Array Expr) : MetaM Expr := do
  if h : 0 < vars.size then
    RArray.toExpr type id (RArray.ofFn (vars[·]) h)
  else
    RArray.toExpr type id (RArray.leaf zero)

/--
Reifies `e`, computes its polynomial, and denotes the normal form.
`normalize?` has already rejected roots that the structure does not interpret, so
`.notApplicable` has exactly two causes: the root operator has a non-standard instance (the
reifier turns it into an atom), or `toPoly?` failed because the budget or the exponent
threshold was exceeded.
-/
private def normalizeCore (e : Expr) : NormM CoreResult := do
  let kind ← getKind
  let ec ← canonArith e
  let re? : Option RingExpr ← if kind.isRing then reifyRing? ec (skipVar := false) else reifySemiring? ec
  let some re := re? | return .notApplicable
  if re matches .var _ then return .notApplicable
  -- Number the atoms in `Expr.lt` order. Reification numbered them by first occurrence;
  -- skip the renaming when that order is already sorted.
  let vars := (← get).vars
  let perm := (Array.range vars.size).qsort fun i j => Expr.lt vars[i]! vars[j]!
  let (re, vars) :=
    if perm.zipIdx.all fun (i, j) => i == j then (re, vars)
    else (re.renameVars (Grind.mkVarRename perm), perm.map (vars[·]!))
  -- `inst` is the structure instance the certificate theorem takes: `CommRing`, `Ring`,
  -- `CommSemiring`, or `Semiring`.
  let (type, u, inst, char?, zero) ← match kind with
    | .commRing _ =>
      let ring ← getCommRing
      let char? := ring.charInst?.bind fun (inst, c) => if c != 0 then some (inst, c) else none
      pure (ring.type, ring.u, ring.commRingInst, char?, mkApp (← getNatCastFn) (mkNatLit 0))
    | .ring _ =>
      let ring ← getRing
      let char? := ring.charInst?.bind fun (inst, c) => if c != 0 then some (inst, c) else none
      pure (ring.type, ring.u, ring.ringInst, char?, mkApp (← getNatCastFn) (mkNatLit 0))
    | .commSemiring _ =>
      let sr ← getCommSemiring
      pure (sr.type, sr.u, sr.commSemiringInst, none, mkApp (← getNatCastFn') (mkNatLit 0))
    | .semiring _ =>
      let sr ← getSemiring
      pure (sr.type, sr.u, sr.semiringInst, none, mkApp (← getNatCastFn') (mkNatLit 0))
  let opts ← getOptions
  let cfg : PolyConfig := {
    char? := char?.map (·.2)
    semiring := !kind.isRing
    commutative := kind.isComm
    maxTerms? := some (sym.arith.maxTerms.get opts)
    maxDegree? := some (sym.arith.maxDegree.get opts)
  }
  let some p ← (toPoly? re).run cfg | return .notApplicable
  -- Fields: inverse atoms with a discharged side condition are cancelled, and in
  -- characteristic zero the numeral inverses become rational coefficients.
  let isField ← isFieldKind kind
  let fc? ← fieldChar0?
  let invs ← if fc?.isSome then getInvVars vars else pure #[]
  let ainvs ← if isField then getInvAtoms vars p else pure #[]
  let ainvsL := invAtomsList ainvs
  let (re', vars, invs) ←
    if !invs.isEmpty then mkPolyQExpr (p.toPolyQ invs.toList ainvsL) vars invs
    else if !ainvs.isEmpty then pure ((p.cancelInvs ainvsL).toExpr, vars, invs)
    else pure (p.toExpr, vars, invs)
  let e' ← if kind.isRing then share (← denoteRingExpr' vars re') else share (← denoteSemiringExpr' vars re')
  if isSameExpr e' e then
    return .normal
  let ctx ← mkContext type zero vars
  let hoka ← if ainvs.isEmpty then pure (mkConst ``True.intro) else pure (mkInvAtomsOk (← getCommRing) ctx vars ainvs)
  let ainvsE := toExpr ainvsL
  let h ← if !invs.isEmpty then
    let (fieldInst, charInst) := fc?.get!
    let invsE := toExpr invs.toList
    let thm := mkApp3 (mkConst ``Grind.CommRing.Expr.eq_of_toPolyQ_eq [u]) type fieldInst charInst
    pure (mkApp8 thm ctx invsE (mkInvVarsOk type u ctx invsE) ainvsE hoka (toExpr re) (toExpr re') eagerReflBoolTrue)
  else if !ainvs.isEmpty then
    let thm := mkApp2 (mkConst ``Grind.CommRing.Expr.eq_of_cancelInvs_eq [u]) type inst
    pure (mkApp6 thm ctx ainvsE hoka (toExpr re) (toExpr re') eagerReflBoolTrue)
  else
    let thm := match kind, char? with
      | .commRing _, some (charInst, c) => mkApp4 (mkConst ``Grind.CommRing.Expr.eq_of_toPolyC_eq [u]) type (toExpr c) inst charInst
      | .commRing _, none => mkApp2 (mkConst ``Grind.CommRing.Expr.eq_of_toPoly_eq [u]) type inst
      | .ring _, some (charInst, c) => mkApp4 (mkConst ``Grind.CommRing.Expr.eq_of_toPolyC_nc_eq [u]) type (toExpr c) inst charInst
      | .ring _, none => mkApp2 (mkConst ``Grind.CommRing.Expr.eq_of_toPoly_nc_eq [u]) type inst
      | .commSemiring _, _ => mkApp2 (mkConst ``Grind.CommRing.eq_normS [u]) type inst
      | .semiring _, _ => mkApp2 (mkConst ``Grind.CommRing.eq_normS_nc [u]) type inst
    pure (mkApp4 thm ctx (toExpr re) (toExpr re') eagerReflBoolTrue)
  return .step e' (mkExpectedPropHint h (mkApp3 (mkConst ``Eq [u.succ]) type e e'))

/--
Runs `core`, and when it reports side conditions `x ≠ 0` for inverse atoms (`invCands`), asks
`discharge?` for each and reruns it with the proved ones. The flag is `true` when a side
condition was asked for, whatever the outcome: the result then depends on the local context.
-/
private def runCore [Monad m] [MonadLiftT SymM m] (kind : Kind) (discharge? : Expr → m (Option Expr))
    (core : NormM CoreResult) : m (CoreResult × Bool) := do
  let run (atomInvs : Array (Expr × Expr × Expr)) : m (CoreResult × Array (Expr × Expr × Expr)) := do
    let (r, s) ← ((core.run { kind, atomInvs }).run {} : SymM _)
    return (r, s.invCands)
  let (r, cands) ← run #[]
  if cands.isEmpty then return (r, false)
  let mut proved := #[]
  for (inv, x, prop) in cands do
    if let some h ← discharge? prop then proved := proved.push (inv, x, h)
  if proved.isEmpty then return (r, true)
  return ((← run proved).1, true)

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
private def gcdMonCoeffs : Poly → Nat
  | .num _ => 0
  | .add k _ p => Nat.gcd k.natAbs (gcdMonCoeffs p)

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

/--
Given the reified sides `l`, `r` of `e := rel lhs rhs` (atoms already numbered in order),
returns the normalized relation. `relFn` is the canonical `Eq α`/`LE.le α inst`/`LT.lt α inst`,
`order?` the order classification, required for `≤` and `<`, and `lhsC`, `rhsC` the sides after
`canonArith`.
-/
private def normalizeRelCore (rel : RelKind) (relFn : Expr) (order? : Option Order) (e lhs rhs lhsC rhsC : Expr)
    (l r : RingExpr) (vars : Array Expr) (lhsOnly : Bool) : NormM CoreResult := do
  let kind ← getKind
  let opts ← getOptions
  let budget : PolyConfig := { maxTerms? := some (sym.arith.maxTerms.get opts), maxDegree? := some (sym.arith.maxDegree.get opts) }
  let budget := { budget with commutative := kind.isComm }
  if kind.isRing then
    let ring ← getRing
    let u := ring.u
    -- Instance for the certificate theorem: `CommRing` or `Ring`.
    let inst ← if kind.isComm then pure (← getCommRing).commRingInst else pure ring.ringInst
    let char? := ring.charInst?.bind fun (inst, c) => if c != 0 then some (inst, c) else none
    -- `simp +arith` leaves equations between atoms and numerals alone (`x = y`, `x = 3`,
    -- `3 = x`): `grind` and other tactics handle these directly. Canonicalization may still
    -- have changed a numeral (`(7 : Fin 5)` is `2`).
    if lhsOnly && rel == .eq then
      match l, r with
      | .var _, .var _ | .var _, .num _ | .num _, .var _ =>
        let e' ← share (mkApp2 relFn lhsC rhsC)
        if isSameExpr e' e then return .normal
        return .step e' (mkExpectedPropHint (mkApp2 (mkConst ``Eq.refl [1]) (mkSort .zero) e') (mkPropEq e e'))
      | _, _ => pure ()
    let some p ← (toPoly? (l.sub r)).run { budget with char? := char?.map (·.2) } | return .notApplicable
    -- Fields: cancel the discharged inverse atoms; in characteristic zero, split the numerator
    -- of `lhs - rhs`, whose denominator's sign needs `IsLinearOrder` for `≤`/`<`.
    let isField ← isFieldKind kind
    let fc? ← fieldChar0?
    let mut invs ← if fc?.isSome then getInvVars vars else pure #[]
    let ainvs ← if isField then getInvAtoms vars p else pure #[]
    let ainvsL := invAtomsList ainvs
    let linInst? ← if invs.isEmpty || rel == .eq then pure none else
      MonadCanon.synthInstance? (mkApp2 (mkConst ``Std.IsLinearOrder [u]) ring.type order?.get!.leInst)
    if rel != .eq && linInst?.isNone then invs := #[]
    let p := if !invs.isEmpty then (p.toPolyQ invs.toList ainvsL).num
      else if !ainvs.isEmpty then p.cancelInvs ainvsL
      else p
    -- `Int`: like `simp +arith`, divide the coefficients by their gcd `k` (`p = k * q + c`).
    -- An equation whose constant is not divisible by `k` is `False`, and `≤` is tightened by
    -- rounding the constant up. `<` is left to the `Int.lt_eq` rewrite. `tight?` records
    -- `(q, k, c)` for the certificate (`IntSolver.lean`).
    let mut p := p
    let mut tight? : Option (Poly × Int × Int) := none
    if kind.isComm && ring.type.isConstOf ``Int && invs.isEmpty && ainvs.isEmpty && char?.isNone && rel != .lt then
      let k := gcdMonCoeffs p
      if k > 1 then
        let c := polyConst p
        let q := divMonCoeffs k p
        if rel == .eq && c % k != 0 then
          let ctx ← mkContext ring.type (mkApp (← getNatCastFn) (mkNatLit 0)) vars
          let h := mkApp7 (mkConst ``Grind.CommRing.eq_norm_unsat_expr) ctx (toExpr l) (toExpr r) (toExpr q) (toExpr (k : Int)) (toExpr c) eagerReflBoolTrue
          let e' ← getFalseExpr
          return .step e' (mkExpectedPropHint h (mkPropEq e e'))
        p := q.addConst (if rel == .eq then c / k else cdiv c k)
        tight? := some (q, k, c)
    -- Nonzero characteristic `c`, `lhsOnly`: when `p` is `k * m + k'` or `k * m₁ - k * m₂` and
    -- `k` has an inverse modulo `c`, multiply by it, so that the equation is solved for `m`
    -- below. `scale?` records `k` and its inverse for the certificate.
    let mut scale? : Option (Int × Int) := none
    if lhsOnly && rel == .eq && kind.isComm && ainvs.isEmpty then
      if let some (_, c) := char? then
        if let some k := solvableCoeff? c p then
          if k != 1 then
            if let some k' := modInv? k c then
              p := p.mulConstC k' c
              scale? := some (k, k')
    -- Like `simp +arith`, an equation already of the form `p = 0` is left alone, and the
    -- equations `x = y` and `x = k` are kept in that form instead of `x - y = 0`.
    if lhsOnly && rel == .eq && char?.isNone && r == .num 0 && p.toExpr == l then return .normal
    let (lp, rp) :=
      if lhsOnly then
        match rel, char?, p with
        | .eq, none, .add 1 m₁ (.add (-1) m₂ (.num 0)) => (.add 1 m₁ (.num 0), .add 1 m₂ (.num 0))
        | .eq, none, .add (-1) m₂ (.add 1 m₁ (.num 0)) => (.add 1 m₁ (.num 0), .add 1 m₂ (.num 0))
        | .eq, none, .add 1 m (.num k) => (.add 1 m (.num 0), .num (-k))
        | .eq, some (_, c), .add 1 m₁ (.add k m₂ (.num 0)) =>
          if k + 1 == c then (.add 1 m₁ (.num 0), .add 1 m₂ (.num 0)) else (p, .num 0)
        | .eq, some (_, c), .add 1 m (.num k) => (.add 1 m (.num 0), .num ((c - k) % c))
        | _, _, _ => (p, .num 0)
      else
        let (lp, rp, c) := splitPoly (char?.map (·.2)) p
        (if c > 0 then lp.addConst c else lp, if c < 0 then rp.addConst (-c) else rp)
    let l' := lp.toExpr
    let r' := rp.toExpr
    let e' ← share (mkApp2 relFn (← denoteRingExpr' vars l') (← denoteRingExpr' vars r'))
    if isSameExpr e' e then return .normal
    let ctx ← mkContext ring.type (mkApp (← getNatCastFn) (mkNatLit 0)) vars
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
      pure (mkApp10 h ctx invsE (mkInvVarsOk ring.type u ctx invsE) ainvsE hoka (toExpr l) (toExpr r) (toExpr l') (toExpr r') eagerReflBoolTrue)
    return .step e' (mkExpectedPropHint h (mkPropEq e e'))
  else
    let sr ← getSemiring
    let u := sr.u
    -- Instance for `eq_normS` / `eq_normS_nc`: `CommSemiring` or `Semiring`.
    let (inst, normS) ← if kind.isComm then
        pure ((← getCommSemiring).commSemiringInst, ``Grind.CommRing.eq_normS)
      else
        pure (sr.semiringInst, ``Grind.CommRing.eq_normS_nc)
    let cfg := { budget with semiring := true }
    let some pl ← (toPoly? l).run cfg | return .notApplicable
    let some pr ← (toPoly? r).run cfg | return .notApplicable
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
    let ctx ← mkContext sr.type (mkApp (← getNatCastFn') (mkNatLit 0)) vars
    -- Term steps `lhs = lhs' + c` and `rhs = rhs' + c` (without `+ c` when nothing is cancelled).
    let mkTermStep (x xC : RingExpr) (ex exC : Expr) : Expr :=
      mkExpectedPropHint
        (mkApp6 (mkConst normS [u]) sr.type inst ctx (toExpr x) (toExpr xC) eagerReflBoolTrue)
        (mkApp3 (mkConst ``Eq [u.succ]) sr.type ex exC)
    let (lC, rC) : RingExpr × RingExpr := if hasC then (.add l' c.toExpr, .add r' c.toExpr) else (l', r')
    let elC ← if hasC then share (← denoteSemiringExpr' vars lC) else pure el
    let erC ← if hasC then share (← denoteSemiringExpr' vars rC) else pure er
    let r₁ : Result := if isSameExpr lhs elC then .rfl else .step elC (mkTermStep l lC lhs elC)
    let r₂ : Result := if isSameExpr rhs erC then .rfl else .step erC (mkTermStep r rC rhs erC)
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

/-- The `normalize?` path for relations; `e` is `rel lhs rhs` with carrier `α`. -/
private def normalizeRel? [Monad m] [MonadLiftT SymM m] [MonadLiftT MetaM m]
    (rel : RelKind) (α e lhs rhs : Expr) (simpAtom : Expr → m Result) (discharge? : Expr → m (Option Expr))
    (lhsOnly : Bool) (commutative : Bool) : m Result := do
  let kind ← match (← (classify? α (commutative := commutative) : SymM _)) with
    | .commRing id => pure (Kind.commRing id)
    | .commSemiring id => pure (Kind.commSemiring id)
    | .nonCommRing id => pure (Kind.ring id)
    | .nonCommSemiring id => pure (Kind.semiring id)
    | .none => return .rfl
  let order? ← match rel with
    | .eq => pure none
    | .le | .lt =>
      let some id ← classifyOrder? α | return .rfl
      let o := (← getArithState).orders[id]!
      unless o.orderedRingInst?.isSome do return .rfl
      if rel == .lt then unless o.lawfulOrderLTInst?.isSome do return .rfl
      -- The relation's instance must be the classified one; compare the canonicalized prefix.
      let fn := if rel == .le then o.leFn else o.ltFn?.get!
      let ok ← liftNorm kind do return isSameExpr fn (← canonExpr e.appFn!.appFn!)
      unless ok do return .rfl
      pure (some o)
  let isField ← isFieldKind kind
  let r₁ ← visitAtoms kind isField simpAtom lhs
  let r₂ ← visitAtoms kind isField simpAtom rhs
  let r₀ ← match h : e with
    | .app fa@h':(.app f a) b => congrBin e fa f a b r₁ r₂ h h'
    | _ => unreachable!
  let e₁ := r₀.getResultExpr e
  let lhs₁ := e₁.appFn!.appArg!
  let rhs₁ := e₁.appArg!
  let relFn := match rel, order? with
    | .eq, _ => e₁.appFn!.appFn!
    | .le, some o => o.leFn
    | .lt, some o => o.ltFn?.get!
    | _, none => e₁.appFn!.appFn!
  let core : NormM CoreResult := do
    let lhsC ← canonArith lhs₁
    let rhsC ← canonArith rhs₁
    let reify (x : Expr) : NormM (Option RingExpr) :=
      if kind.isRing then reifyRing? x (skipVar := false) else reifySemiring? x
    let some l ← reify lhsC | return .notApplicable
    let some r ← reify rhsC | return .notApplicable
    -- No shortcut when both sides are atoms: `x ≤ x` must become `0 ≤ 0`, and a relation
    -- between distinct atoms normalizes to itself.
    let vars := (← get).vars
    let perm := (Array.range vars.size).qsort fun i j => Expr.lt vars[i]! vars[j]!
    let (l, r, vars) :=
      if perm.zipIdx.all fun (i, j) => i == j then (l, r, vars)
      else
        let f := Grind.mkVarRename perm
        (l.renameVars f, r.renameVars f, perm.map (vars[·]!))
    normalizeRelCore rel relFn order? e₁ lhs₁ rhs₁ lhsC rhsC l r vars lhsOnly
  let (r, cd) ← runCore kind discharge? core
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
that asked for one is `contextDependent`.
-/
private def normalizeTerm? [Monad m] [MonadLiftT SymM m] [MonadLiftT MetaM m] (e : Expr) (simpAtom : Expr → m Result)
    (discharge? : Expr → m (Option Expr)) (commutative : Bool) : m Result := do
  let some α := getArithType? e | return .rfl
  let kind ← match (← (classify? α (commutative := commutative) : SymM _)) with
    | .commRing id => pure (Kind.commRing id)
    | .commSemiring id => pure (Kind.commSemiring id)
    | .nonCommRing id => pure (Kind.ring id)
    | .nonCommSemiring id => pure (Kind.semiring id)
    | .none => return .rfl
  let isRing := kind.isRing
  let isField ← (isFieldKind kind : SymM _)
  -- Roots that the structure does not interpret are atoms; after this check, an atom root
  -- reported by the reifier can only be a non-standard instance.
  match_expr e with
  | HPow.hPow _ _ _ _ _ k => unless (Sym.getNatValue? k).run.isSome do return .rfl
  | HSub.hSub _ _ _ _ _ _ => unless isRing do return .rfl
  | Neg.neg _ _ _ => unless isRing do return .rfl
  | HDiv.hDiv _ _ _ _ _ _ => unless isField do return .rfl
  | Inv.inv _ _ _ => unless isField do return .rfl
  | IntCast.intCast _ _ _ => unless isRing do return .rfl
  | _ => pure ()
  let r₁ ← visitAtoms kind isField simpAtom e
  let e₁ := r₁.getResultExpr e
  let (r, cd) ← runCore kind discharge? (normalizeCore e₁)
  match r with
  | .notApplicable => return if cd then r₁.withContextDependent else r₁
  | .normal => return if cd then r₁.markAsDone.withContextDependent else r₁.markAsDone
  | .step e' h₂ =>
    match r₁ with
    | .rfl _ cd₀ => return .step e' h₂ (done := true) (contextDependent := cd₀ || cd)
    | .step _ h₁ _ cd₀ => mkEqTransResult e e₁ h₁ (.step e' h₂ (done := true) (contextDependent := cd)) cd₀

/-- The `NormM` part of `normalizeDvd?`: `e₁` is `k ∣ arg` with the atoms of `arg` simplified. -/
private def normalizeDvdCore (e₁ dvdFn : Expr) (k : Int) : NormM CoreResult := do
  let argC ← canonArith e₁.appArg!
  let some x ← reifyRing? argC (skipVar := false) | return .notApplicable
  let vars := (← get).vars
  let perm := (Array.range vars.size).qsort fun i j => Expr.lt vars[i]! vars[j]!
  let (x, vars) :=
    if perm.zipIdx.all fun (i, j) => i == j then (x, vars)
    else
      let f := Grind.mkVarRename perm
      (x.renameVars f, perm.map (vars[·]!))
  let ring ← getRing
  let opts ← getOptions
  let budget : PolyConfig := { maxTerms? := some (sym.arith.maxTerms.get opts), maxDegree? := some (sym.arith.maxDegree.get opts) }
  let some p ← (toPoly? x).run budget | return .notApplicable
  let g : Nat := Nat.gcd k.natAbs (gcdMonCoeffs p)
  let c := polyConst p
  let q := divMonCoeffs g p
  let ctx ← mkContext ring.type (mkApp (← getNatCastFn) (mkNatLit 0)) vars
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

/--
The `normalize?` path for `k ∣ arg` over `Int` with a numeral `k ≠ 0`; `dvdFn` is
`Dvd.dvd Int inst`. Like `simp +arith`, the constraint is divided by the gcd `g` of `k` and
the coefficients of `arg`: `k ∣ g * q + c` becomes `False` when `g ∤ c`, and `k / g ∣ q + c / g`
otherwise (`IntSolver.lean`).
-/
private def normalizeDvd? [Monad m] [MonadLiftT SymM m] [MonadLiftT MetaM m]
    (e dvdFn arg : Expr) (k : Int) (simpAtom : Expr → m Result) (discharge? : Expr → m (Option Expr)) : m Result := do
  let kind ← match (← (classify? dvdFn.appFn!.appArg! : SymM _)) with
    | .commRing id => pure (Kind.commRing id)
    | _ => return .rfl
  let r₁ ← visitAtoms kind false simpAtom arg
  let r₀ ← match h : e with
    | .app f a => (Simp.mkCongrArg e f a r₁ h : SymM Result)
    | _ => unreachable!
  let e₁ := r₀.getResultExpr e
  let core := normalizeDvdCore e₁ dvdFn k
  let (r, cd) ← runCore kind discharge? core
  match r with
  | .notApplicable => return if cd then r₀.withContextDependent else r₀
  | .normal => return if cd then r₀.markAsDone.withContextDependent else r₀.markAsDone
  | .step e' h₂ =>
    match r₀ with
    | .rfl _ cd₀ => return .step e' h₂ (done := true) (contextDependent := cd₀ || cd)
    | .step _ h₁ _ cd₀ => mkEqTransResult e e₁ h₁ (.step e' h₂ (done := true) (contextDependent := cd)) cd₀

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

With `commutative := false`, multiplication keeps the order of its factors even when the
carrier has a commutative ring or semiring instance. The noncommutative certificates are used,
and field normalization and integer gcd/divisibility normalization are disabled.
-/
def normalize? [Monad m] [MonadLiftT SymM m] [MonadLiftT MetaM m] (e : Expr) (simpAtom : Expr → m Result)
    (discharge? : Expr → m (Option Expr) := fun _ => pure none) (lhsOnly : Bool := false)
    (commutative : Bool := true) : m Result := do
  match_expr e with
  | Eq α lhs rhs => normalizeRel? .eq α e lhs rhs simpAtom discharge? lhsOnly commutative
  | LE.le α _ lhs rhs => normalizeRel? .le α e lhs rhs simpAtom discharge? lhsOnly commutative
  | LT.lt α _ lhs rhs => normalizeRel? .lt α e lhs rhs simpAtom discharge? lhsOnly commutative
  | Dvd.dvd α _ k arg =>
    if commutative && α.isConstOf ``Int then
      if let some kv := (Sym.getIntValue? k).run then
        if kv != 0 then
          return ← normalizeDvd? e e.appFn!.appFn! arg kv simpAtom discharge?
    normalizeTerm? e simpAtom discharge? commutative
  | _ => normalizeTerm? e simpAtom discharge? commutative

end Lean.Meta.Sym.Arith
