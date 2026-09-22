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
import Lean.Meta.Sym.Arith.VarRename
import Lean.Meta.Sym.Arith.ToExpr
public import Lean.Meta.Sym.Simp.App
import Lean.Meta.AppBuilder
import Lean.Meta.Sym.AlphaShareBuilder
import Lean.Data.RArray
public section
namespace Lean.Meta.Sym.Arith
open Lean.Meta.Sym.Simp (Result mkEqTransResult)
open Lean.Meta.Sym.Internal (mkAppS mkAppS₂)

/-!
# Polynomial normalization of ring and semiring terms

`normalize?` rewrites a term of a `CommRing` or `CommSemiring` into the polynomial normal
form of `Poly.toExpr`, with a proof by reflection: the certificate compares the `Init`
polynomial of the input with the polynomial of the output (`Expr.eq_of_toPoly_eq`,
`Expr.eq_of_toPolyC_eq`, `eq_normS`).

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
  deriving Inhabited

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

private def congrBin (e f a b : Expr) (ra rb : Result) (h : e = .app (.app f a) b) : m Result := do
  let r ← (Simp.mkCongrArg (.app f a) f a ra rfl : SymM Result)
  Simp.mkCongr e (.app f a) b r rb h

private partial def visitAtoms (isRing : Bool) (simpAtom : Expr → m Result) (e : Expr) : m Result := do
  let bin : m Result := do
    match h : e with
    | .app (.app f a) b => congrBin e f a b (← visitAtoms isRing simpAtom a) (← visitAtoms isRing simpAtom b) h
    | _ => unreachable!
  let un : m Result := do
    match h : e with
    | .app f a => (Simp.mkCongrArg e f a (← visitAtoms isRing simpAtom a) h : SymM Result)
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
    | .app (.app f a) k => congrBin e f a k (← visitAtoms isRing simpAtom a) .rfl h
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
  let isRing := (← getKind) matches .commRing _
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
  let re? : Option RingExpr ← match kind with
    | .commRing _ => reifyRing? ec (skipVar := false)
    | .commSemiring _ => reifySemiring? ec
  let some re := re? | return .notApplicable
  if re matches .var _ then return .notApplicable
  -- Number the atoms in `Expr.lt` order. Reification numbered them by first occurrence;
  -- skip the renaming when that order is already sorted.
  let vars := (← get).vars
  let perm := (Array.range vars.size).qsort fun i j => Expr.lt vars[i]! vars[j]!
  let (re, vars) :=
    if perm.zipIdx.all fun (i, j) => i == j then (re, vars)
    else (re.renameVars (Grind.mkVarRename perm), perm.map (vars[·]!))
  let (type, u, inst, char?, zero) ← match kind with
    | .commRing _ =>
      let ring ← getCommRing
      let char? := ring.charInst?.bind fun (inst, c) => if c != 0 then some (inst, c) else none
      pure (ring.type, ring.u, ring.commRingInst, char?, mkApp (← getNatCastFn) (mkNatLit 0))
    | .commSemiring _ =>
      let sr ← getCommSemiring
      pure (sr.type, sr.u, sr.commSemiringInst, none, mkApp (← getNatCastFn') (mkNatLit 0))
  let opts ← getOptions
  let cfg : PolyConfig := {
    char? := char?.map (·.2)
    semiring := kind matches .commSemiring _
    maxTerms? := some (sym.arith.maxTerms.get opts)
    maxDegree? := some (sym.arith.maxDegree.get opts)
  }
  let some p ← (toPoly? re).run cfg | return .notApplicable
  let re' := p.toExpr
  let e' ← match kind with
    | .commRing _ => share (← denoteRingExpr' vars re')
    | .commSemiring _ => share (← denoteSemiringExpr' vars re')
  if isSameExpr e' e then
    return .normal
  let ctx ← mkContext type zero vars
  let h := match kind, char? with
    | .commRing _, some (charInst, c) =>
      mkApp8 (mkConst ``Grind.CommRing.Expr.eq_of_toPolyC_eq [u]) type (toExpr c) inst charInst ctx (toExpr re) (toExpr re') eagerReflBoolTrue
    | .commRing _, none =>
      mkApp6 (mkConst ``Grind.CommRing.Expr.eq_of_toPoly_eq [u]) type inst ctx (toExpr re) (toExpr re') eagerReflBoolTrue
    | .commSemiring _, _ =>
      mkApp6 (mkConst ``Grind.CommRing.eq_normS [u]) type inst ctx (toExpr re) (toExpr re') eagerReflBoolTrue
  return .step e' (mkExpectedPropHint h (mkApp3 (mkConst ``Eq [u.succ]) type e e'))

/--
Normalizes the arithmetic term `e` (an application of `+`, `-`, `*`, `^`, or negation whose
carrier type is a `CommRing` or `CommSemiring`) into polynomial normal form, after simplifying
its atoms with `simpAtom`. `e` must be maximally shared.

The result distinguishes three cases:
* `.rfl`: the normalizer does not apply (`e` is not such a term, or it is an atom for its
  structure, or the polynomial exceeds the `sym.arith.maxTerms`/`sym.arith.maxDegree` budget
  or the exponent threshold, in which case an issue is reported). If `simpAtom` rewrote atoms,
  the result is that rewrite instead, with `done := false`, so that a simplifier still visits
  the subterms.
* `.rfl (done := true)` (or the atom rewrite marked `done`): `e` is already in normal form.
* `.step e' h (done := true)`: `e` normalizes to `e'`.
-/
def normalize? [Monad m] [MonadLiftT SymM m] [MonadLiftT MetaM m] (e : Expr) (simpAtom : Expr → m Result) : m Result := do
  let some α := getArithType? e | return .rfl
  let kind ← match (← (classify? α : SymM _)) with
    | .commRing id => pure (Kind.commRing id)
    | .commSemiring id => pure (Kind.commSemiring id)
    | _ => return .rfl
  let isRing := kind matches .commRing _
  -- Roots that the structure does not interpret are atoms; after this check, an atom root
  -- reported by the reifier can only be a non-standard instance.
  match_expr e with
  | HPow.hPow _ _ _ _ _ k => unless (Sym.getNatValue? k).run.isSome do return .rfl
  | HSub.hSub _ _ _ _ _ _ => unless isRing do return .rfl
  | Neg.neg _ _ _ => unless isRing do return .rfl
  | _ => pure ()
  let r₁ ← visitAtoms isRing simpAtom e
  let e₁ := r₁.getResultExpr e
  match (← ((normalizeCore e₁).run { kind } |>.run' {} : SymM CoreResult)) with
  | .notApplicable => return r₁
  | .normal => return r₁.markAsDone
  | .step e' h₂ =>
    match r₁ with
    | .rfl _ cd => return .step e' h₂ (done := true) (contextDependent := cd)
    | .step _ h₁ _ cd => mkEqTransResult e e₁ h₁ (.step e' h₂ (done := true)) cd

end Lean.Meta.Sym.Arith
