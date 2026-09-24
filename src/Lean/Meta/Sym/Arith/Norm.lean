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
public section
namespace Lean.Meta.Sym.Arith
open Lean.Meta.Sym.Simp (Result mkEqTransResult)
open Lean.Meta.Sym.Internal (mkAppS mkAppS₂)

/-!
# Polynomial normalization of ring and semiring terms

`normalize?` rewrites a term of a `CommRing`, `Ring`, `CommSemiring`, or `Semiring` into the
polynomial normal form of `Poly.toExpr`, with a proof by reflection: the certificate compares
the `Init` polynomial of the input with the polynomial of the output (`Expr.eq_of_toPoly_eq`,
`Expr.eq_of_toPolyC_eq`, `eq_normS`, and their `_nc` variants for the non-commutative
structures, where monomials keep the order of their factors).

The normalizer owns the traversal of the arithmetic tree: it recurses through the operators
its structure interprets and hands every atom (maximal non-arithmetic subterm) to the
`simpAtom` callback, so that a simplifier can rewrite the atoms before reification and the
normal form is stated for the simplified atoms. The congruence proof for that step is built
with `Sym.Simp.mkCongr`.

Atoms are numbered in `Expr.lt` order, so the normal form of a term does not depend on the
order in which its atoms occur, and two terms denoting the same polynomial over the same
atoms normalize to the same (maximally shared) expression.

The input is not assumed to be canonicalized. Reification runs on a copy of the term whose
operator prefixes (`HAdd.hAdd α α α inst`, ...) and numerals are canonicalized (`canonArith`);
the atoms are shared with the original, the proof is stated for the original term, and the
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

structure NormM.State where
  vars   : Array Expr := #[]
  varMap : PHashMap ExprPtr Var := {}

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

/-- If `e` is an application of an arithmetic operator supported by the normalizer, returns its carrier type. -/
def getArithType? (e : Expr) : Option Expr :=
  match_expr e with
  | HAdd.hAdd α _ _ _ _ _ => some α
  | HSub.hSub α _ _ _ _ _ => some α
  | HMul.hMul α _ _ _ _ _ => some α
  | HPow.hPow α β _ _ _ _ => if β.isConstOf ``Nat then some α else none
  | HSMul.hSMul σ α _ _ _ _ => if σ.isConstOf ``Nat || σ.isConstOf ``Int then some α else none
  | Neg.neg α _ _ => some α
  | _ => none

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

private def congrBin (e f a b : Expr) (ra rb : Result) (h : e = .app (.app f a) b) : m Result := do
  let r ← (Simp.mkCongrArg (.app f a) f a ra rfl : SymM Result)
  Simp.mkCongr e (.app f a) b r rb h

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

private partial def visitAtoms (kind : Kind) (simpAtom : Expr → m Result) (e : Expr) : m Result := do
  let isRing := kind.isRing
  let bin : m Result := do
    match h : e with
    | .app (.app f a) b => congrBin e f a b (← visitAtoms kind simpAtom a) (← visitAtoms kind simpAtom b) h
    | _ => unreachable!
  let un : m Result := do
    match h : e with
    | .app f a => (Simp.mkCongrArg e f a (← visitAtoms kind simpAtom a) h : SymM Result)
    | _ => unreachable!
  match_expr e with
  | HAdd.hAdd _ _ _ _ _ _ => bin
  | HMul.hMul _ _ _ _ _ _ => bin
  | HSub.hSub _ _ _ _ _ _ => if isRing then bin else simpAtom e
  | Neg.neg _ _ _ => if isRing then un else simpAtom e
  | HPow.hPow _ _ _ _ _ k =>
    -- Only literal exponents are interpreted; the exponent is not simplified.
    unless (Sym.getNatValue? k).run.isSome do return (← simpAtom e)
    match h : e with
    | .app (.app f a) k => congrBin e f a k (← visitAtoms kind simpAtom a) .rfl h
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
    | .app (.app f k) a =>
      let r₁ ← congrBin e f k a (← simpAtom k) (← visitAtoms kind simpAtom a) h
      let e₁ := r₁.getResultExpr e
      let (e₂, h₂) ← liftNorm kind (mkSMulStep kind isNat e₁ e₁.appFn!.appArg! e₁.appArg!)
      match r₁ with
      | .rfl _ cd => return .step e₂ h₂ (contextDependent := cd)
      | .step _ h₁ _ cd => mkEqTransResult e e₁ h₁ (.step e₂ h₂) cd
    | _ => unreachable!
  | NatCast.natCast _ _ a => if (Sym.getNatValue? a).run.isSome then return .rfl else simpAtom e
  | IntCast.intCast _ _ a => if isRing && (Sym.getIntValue? a).run.isSome then return .rfl else simpAtom e
  | OfNat.ofNat _ _ _ => return .rfl
  | _ => simpAtom e

end Visit

/--
Canonicalizes the operator prefixes and the numerals of the arithmetic tree rooted at `e`,
without touching the atoms, so that the reifier's pointer checks against the cached operators
succeed. Nodes that the structure does not interpret (`-` in a semiring, `^` with a symbolic
exponent, casts of non-literals) are atoms. Returns `e` itself when nothing changes.
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
  | NatCast.natCast _ _ a => if (Sym.getNatValue? a).run.isSome then castLit e a else return e
  | IntCast.intCast _ _ a => if isRing && (Sym.getIntValue? a).run.isSome then castLit e a else return e
  | OfNat.ofNat _ _ _ => canonExpr e
  | _ => return e

/-! ## Reflection -/

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
  let re' := p.toExpr
  let e' ← if kind.isRing then share (← denoteRingExpr' vars re') else share (← denoteSemiringExpr' vars re')
  if isSameExpr e' e then
    return .normal
  let ctx ← mkContext type zero vars
  let thm := match kind, char? with
    | .commRing _, some (charInst, c) => mkApp4 (mkConst ``Grind.CommRing.Expr.eq_of_toPolyC_eq [u]) type (toExpr c) inst charInst
    | .commRing _, none => mkApp2 (mkConst ``Grind.CommRing.Expr.eq_of_toPoly_eq [u]) type inst
    | .ring _, some (charInst, c) => mkApp4 (mkConst ``Grind.CommRing.Expr.eq_of_toPolyC_nc_eq [u]) type (toExpr c) inst charInst
    | .ring _, none => mkApp2 (mkConst ``Grind.CommRing.Expr.eq_of_toPoly_nc_eq [u]) type inst
    | .commSemiring _, _ => mkApp2 (mkConst ``Grind.CommRing.eq_normS [u]) type inst
    | .semiring _, _ => mkApp2 (mkConst ``Grind.CommRing.eq_normS_nc [u]) type inst
  let h := mkApp4 thm ctx (toExpr re) (toExpr re') eagerReflBoolTrue
  return .step e' (mkExpectedPropHint h (mkApp3 (mkConst ``Eq [u.succ]) type e e'))

/-! ## Relations

`lhs = rhs`, `lhs ≤ rhs`, `lhs < rhs` over a ring or semiring are normalized by
moving everything to one side and splitting by sign (`x + y = z + 2 * x` becomes `y = z + x`).
Rings use `eq_norm_expr`, `le_norm_expr`, `lt_norm_expr` (`CommSolver.lean`). Semirings have no
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

/--
Given the reified sides `l`, `r` of `e := rel lhs rhs` (atoms already numbered in order),
returns the normalized relation. `relFn` is the canonical `Eq α`/`LE.le α inst`/`LT.lt α inst`,
and `order?` the order classification, required for `≤` and `<`.
-/
private def normalizeRelCore (rel : RelKind) (relFn : Expr) (order? : Option Order) (e lhs rhs : Expr)
    (l r : RingExpr) (vars : Array Expr) : NormM CoreResult := do
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
    let some p ← (toPoly? (l.sub r)).run { budget with char? := char?.map (·.2) } | return .notApplicable
    let (lp, rp, c) := splitPoly (char?.map (·.2)) p
    let lp := if c > 0 then lp.addConst c else lp
    let rp := if c < 0 then rp.addConst (-c) else rp
    let l' := lp.toExpr
    let r' := rp.toExpr
    let e' ← share (mkApp2 relFn (← denoteRingExpr' vars l') (← denoteRingExpr' vars r'))
    if isSameExpr e' e then return .normal
    let ctx ← mkContext ring.type (mkApp (← getNatCastFn) (mkNatLit 0)) vars
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
    let h := mkApp6 h ctx (toExpr l) (toExpr r) (toExpr l') (toExpr r') eagerReflBoolTrue
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
    let rel₁ ← Simp.mkCongr (.app (.app relFn lhs) rhs) (.app relFn lhs) rhs
      (← Simp.mkCongrArg (.app relFn lhs) relFn lhs r₁ rfl) r₂ rfl
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
    (rel : RelKind) (α e lhs rhs : Expr) (simpAtom : Expr → m Result) : m Result := do
  let kind ← match (← (classify? α : SymM _)) with
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
  let r₁ ← visitAtoms kind simpAtom lhs
  let r₂ ← visitAtoms kind simpAtom rhs
  let r₀ ← match h : e with
    | .app (.app f a) b => congrBin e f a b r₁ r₂ h
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
    normalizeRelCore rel relFn order? e₁ lhs₁ rhs₁ l r vars
  match (← liftNorm kind core) with
  | .notApplicable => return r₀
  | .normal => return r₀.markAsDone
  | .step e' h₂ =>
    match r₀ with
    | .rfl _ cd => return .step e' h₂ (done := true) (contextDependent := cd)
    | .step _ h₁ _ cd => mkEqTransResult e e₁ h₁ (.step e' h₂ (done := true)) cd

/--
Normalizes the arithmetic term `e` (an application of `+`, `-`, `*`, `^`, `•`, or negation
whose carrier type is a `CommRing` or `CommSemiring`) into polynomial normal form, after
simplifying its atoms with `simpAtom`. `e` must be maximally shared.

The result distinguishes three cases:
* `.rfl`: the normalizer does not apply (`e` is not such a term, or it is an atom for its
  structure, or the polynomial exceeds the `sym.arith.maxTerms`/`sym.arith.maxDegree` budget
  or the exponent threshold, in which case an issue is reported). If `simpAtom` rewrote atoms,
  the result is that rewrite instead, with `done := false`, so that a simplifier still visits
  the subterms.
* `.rfl (done := true)` (or the atom rewrite marked `done`): `e` is already in normal form.
* `.step e' h (done := true)`: `e` normalizes to `e'`.
-/
private def normalizeTerm? [Monad m] [MonadLiftT SymM m] [MonadLiftT MetaM m] (e : Expr) (simpAtom : Expr → m Result) : m Result := do
  let some α := getArithType? e | return .rfl
  let kind ← match (← (classify? α : SymM _)) with
    | .commRing id => pure (Kind.commRing id)
    | .commSemiring id => pure (Kind.commSemiring id)
    | .nonCommRing id => pure (Kind.ring id)
    | .nonCommSemiring id => pure (Kind.semiring id)
    | .none => return .rfl
  let isRing := kind.isRing
  -- Roots that the structure does not interpret are atoms; after this check, an atom root
  -- reported by the reifier can only be a non-standard instance.
  match_expr e with
  | HPow.hPow _ _ _ _ _ k => unless (Sym.getNatValue? k).run.isSome do return .rfl
  | HSub.hSub _ _ _ _ _ _ => unless isRing do return .rfl
  | Neg.neg _ _ _ => unless isRing do return .rfl
  | _ => pure ()
  let r₁ ← visitAtoms kind simpAtom e
  let e₁ := r₁.getResultExpr e
  match (← ((normalizeCore e₁).run { kind } |>.run' {} : SymM CoreResult)) with
  | .notApplicable => return r₁
  | .normal => return r₁.markAsDone
  | .step e' h₂ =>
    match r₁ with
    | .rfl _ cd => return .step e' h₂ (done := true) (contextDependent := cd)
    | .step _ h₁ _ cd => mkEqTransResult e e₁ h₁ (.step e' h₂ (done := true)) cd

/--
Normalizes `e` into polynomial normal form after simplifying its atoms with `simpAtom`:
either an arithmetic term (see `normalizeTerm?`) or a relation `lhs = rhs`, `lhs ≤ rhs`,
`lhs < rhs` whose carrier type is a `CommRing` or `CommSemiring` (see "Relations").
`e` must be maximally shared. The result cases are those of `normalizeTerm?`. A normalized
relation is `done` as well; a simplifier that wants `post` to see normalized relations (to
close `t = t`, say) must apply it itself, as `Sym.Simp.simpArith` does.
-/
def normalize? [Monad m] [MonadLiftT SymM m] [MonadLiftT MetaM m] (e : Expr) (simpAtom : Expr → m Result) : m Result := do
  match_expr e with
  | Eq α lhs rhs => normalizeRel? .eq α e lhs rhs simpAtom
  | LE.le α _ lhs rhs => normalizeRel? .le α e lhs rhs simpAtom
  | LT.lt α _ lhs rhs => normalizeRel? .lt α e lhs rhs simpAtom
  | _ => normalizeTerm? e simpAtom

end Lean.Meta.Sym.Arith
