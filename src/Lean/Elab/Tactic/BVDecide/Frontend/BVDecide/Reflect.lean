/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Std.Data.HashMap
import Std.Tactic.BVDecide.Bitblast.BVExpr.Basic
import Lean.Meta.AppBuilder
import Lean.ToExpr
import Lean.Data.RArray

/-!
This module contains the implementation of the reflection monad, used by all other components of this
directory.
-/

namespace Lean.Elab.Tactic.BVDecide
namespace Frontend

open Std.Tactic.BVDecide

instance : ToExpr BVBinOp where
  toExpr x :=
    match x with
    | .and => mkConst ``BVBinOp.and
    | .or => mkConst ``BVBinOp.or
    | .xor => mkConst ``BVBinOp.xor
    | .add => mkConst ``BVBinOp.add
    | .mul => mkConst ``BVBinOp.mul
    | .udiv => mkConst ``BVBinOp.udiv
    | .umod => mkConst ``BVBinOp.umod
  toTypeExpr := mkConst ``BVBinOp

instance : ToExpr BVUnOp where
  toExpr x :=
    match x with
    | .not => mkConst ``BVUnOp.not
    | .rotateLeft n => mkApp (mkConst ``BVUnOp.rotateLeft) (toExpr n)
    | .rotateRight n => mkApp (mkConst ``BVUnOp.rotateRight) (toExpr n)
    | .arithShiftRightConst n => mkApp (mkConst ``BVUnOp.arithShiftRightConst) (toExpr n)
  toTypeExpr := mkConst ``BVUnOp

instance : ToExpr (BVExpr w) where
  toExpr x := go x
  toTypeExpr := mkApp (mkConst ``BVExpr) (toExpr w)
where
  go {w : Nat} : BVExpr w → Expr
  | .var idx => mkApp2 (mkConst ``BVExpr.var) (toExpr w) (toExpr idx)
  | .const val => mkApp2 (mkConst ``BVExpr.const) (toExpr w) (toExpr val)
  | .bin lhs op rhs => mkApp4 (mkConst ``BVExpr.bin) (toExpr w) (go lhs) (toExpr op) (go rhs)
  | .un op operand => mkApp3 (mkConst ``BVExpr.un) (toExpr w) (toExpr op) (go operand)
  | .append (w := w) (l := l) (r := r) lhs rhs _ =>
    let wExpr := toExpr w
    let proof := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Nat) wExpr
    mkApp6 (mkConst ``BVExpr.append) (toExpr l) (toExpr r) wExpr (go lhs) (go rhs) proof
  | .replicate (w' := newWidth) (w := oldWidth) w inner _ =>
    let newWExpr := toExpr newWidth
    let proof := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Nat) newWExpr
    mkApp5 (mkConst ``BVExpr.replicate) (toExpr oldWidth) newWExpr (toExpr w) (go inner) proof
  | .extract (w := oldWidth) hi lo expr =>
    mkApp4 (mkConst ``BVExpr.extract) (toExpr oldWidth) (toExpr hi) (toExpr lo) (go expr)
  | .shiftLeft (m := m) (n := n) lhs rhs =>
    mkApp4 (mkConst ``BVExpr.shiftLeft) (toExpr m) (toExpr n) (go lhs) (go rhs)
  | .shiftRight (m := m) (n := n) lhs rhs =>
    mkApp4 (mkConst ``BVExpr.shiftRight) (toExpr m) (toExpr n) (go lhs) (go rhs)
  | .arithShiftRight (m := m) (n := n) lhs rhs =>
    mkApp4 (mkConst ``BVExpr.arithShiftRight) (toExpr m) (toExpr n) (go lhs) (go rhs)

instance : ToExpr BVBinPred where
  toExpr x :=
    match x with
    | .eq => mkConst ``BVBinPred.eq
    | .ult => mkConst ``BVBinPred.ult
  toTypeExpr := mkConst ``BVBinPred

instance : ToExpr Gate where
  toExpr x :=
    match x with
    | .and => mkConst ``Gate.and
    | .xor => mkConst ``Gate.xor
    | .beq => mkConst ``Gate.beq
    | .or => mkConst ``Gate.or
  toTypeExpr := mkConst ``Gate

instance : ToExpr BVPred where
  toExpr x := go x
  toTypeExpr := mkConst ``BVPred
where
  go : BVPred → Expr
  | .bin (w := w) lhs op rhs =>
    mkApp4 (mkConst ``BVPred.bin) (toExpr w) (toExpr lhs) (toExpr op) (toExpr rhs)
  | .getLsbD (w := w) expr idx =>
    mkApp3 (mkConst ``BVPred.getLsbD) (toExpr w) (toExpr expr) (toExpr idx)


instance [ToExpr α] : ToExpr (BoolExpr α) where
  toExpr x := go x
  toTypeExpr := mkApp (mkConst ``BoolExpr) (toTypeExpr α)
where
  go : (BoolExpr α) → Expr
  | .literal lit => mkApp2 (mkConst ``BoolExpr.literal) (toTypeExpr α) (toExpr lit)
  | .const b => mkApp2 (mkConst ``BoolExpr.const) (toTypeExpr α) (toExpr b)
  | .not x => mkApp2 (mkConst ``BoolExpr.not) (toTypeExpr α) (go x)
  | .gate g x y => mkApp4 (mkConst ``BoolExpr.gate) (toTypeExpr α) (toExpr g) (go x) (go y)
  | .ite d l r => mkApp4 (mkConst ``BoolExpr.ite) (toTypeExpr α) (go d) (go l) (go r)


open Lean.Meta

/--
A `BitVec` atom.
-/
structure Atom where
  /--
  The width of the `BitVec` that is being abstracted.
  -/
  width : Nat
  /--
  A unique numeric identifier for the atom.
  -/
  atomNumber : Nat
  /--
  Whether the atom is synthetic. The effect of this is that values for this atom are not considered
  for the counter example deriviation. This is for example useful when we introduce an atom over
  an expression, together with additional lemmas that fully describe the behavior of the atom.
  -/
  synthetic : Bool

/--
The state of the reflection monad
-/
structure State where
  /--
  The atoms encountered so far. Saved as a map from `BitVec` expressions to a (width, atomNumber)
  pair.
  -/
  atoms : Std.HashMap Expr Atom := {}
  /--
  A cache for `atomsAssignment`. If it is `none` the cache is currently invalidated as new atoms
  have been added since it was last updated, if it is `some` it must be consistent with the atoms
  contained in `atoms`.
  -/
  atomsAssignmentCache : Option Expr := none
  /--
  Cached calls to `evalsAtAtoms` of various reflection structures. Whenever `atoms` is modified
  this cache is invalidated as `evalsAtAtoms` relies on `atoms`.
  -/
  evalsAtCache : Std.HashMap Expr (Option Expr) := {}

/--
The reflection monad, used to track `BitVec` variables that we see as we traverse the context.
-/
abbrev M := StateRefT State MetaM

/--
A reified version of an `Expr` representing a `BVExpr`.
-/
structure ReifiedBVExpr where
  width : Nat
  /--
  The reified expression.
  -/
  bvExpr : BVExpr width
  /--
  The expression that was reflected, used for caching of `evalsAtAtoms`.
  -/
  originalExpr : Expr
  /--
  A proof that `bvExpr.eval atomsAssignment = originalExpr`, none if it holds by `rfl`.
  -/
  evalsAtAtoms' : M (Option Expr)
  /--
  A cache for `toExpr bvExpr`.
  -/
  expr : Expr

def ReifiedBVExpr.evalsAtAtoms (reified : ReifiedBVExpr) : M (Option Expr) := do
  match (← get).evalsAtCache[reified.originalExpr]? with
  | some hit => return hit
  | none =>
    let proof? ← reified.evalsAtAtoms'
    modify fun s => { s with evalsAtCache :=  s.evalsAtCache.insert reified.originalExpr proof? }
    return proof?

/--
A reified version of an `Expr` representing a `BVPred`.
-/
structure ReifiedBVPred where
  /--
  The reified expression.
  -/
  bvPred : BVPred
  /--
  The expression that was reflected, usef for caching of `evalsAtAtoms`.
  -/
  originalExpr : Expr
  /--
  A proof that `bvPred.eval atomsAssignment = originalExpr`, none if it holds by `rfl`.
  -/
  evalsAtAtoms' : M (Option Expr)
  /--
  A cache for `toExpr bvPred`
  -/
  expr : Expr

def ReifiedBVPred.evalsAtAtoms (reified : ReifiedBVPred) : M (Option Expr) := do
  match (← get).evalsAtCache[reified.originalExpr]? with
  | some hit => return hit
  | none =>
    let proof? ← reified.evalsAtAtoms'
    modify fun s => { s with evalsAtCache :=  s.evalsAtCache.insert reified.originalExpr proof? }
    return proof?

/--
A reified version of an `Expr` representing a `BVLogicalExpr`.
-/
structure ReifiedBVLogical where
  /--
  The reified expression.
  -/
  bvExpr : BVLogicalExpr
  /--
  The expression that was reflected, usef for caching of `evalsAtAtoms`.
  -/
  originalExpr : Expr
  /--
  A proof that `bvExpr.eval atomsAssignment = originalExpr`, none if it holds by `rfl`.
  -/
  evalsAtAtoms' : M (Option Expr)
  /--
  A cache for `toExpr bvExpr`
  -/
  expr : Expr

def ReifiedBVLogical.evalsAtAtoms (reified : ReifiedBVLogical) : M (Option Expr) := do
  match (← get).evalsAtCache[reified.originalExpr]? with
  | some hit => return hit
  | none =>
    let proof? ← reified.evalsAtAtoms'
    modify fun s => { s with evalsAtCache :=  s.evalsAtCache.insert reified.originalExpr proof? }
    return proof?

/--
A reified version of an `Expr` representing a `BVLogicalExpr` that we know to be true.
-/
structure SatAtBVLogical where
  /--
  The reified expression.
  -/
  bvExpr : BVLogicalExpr
  /--
  A proof that `bvExpr.eval atomsAssignment = true`.
  -/
  satAtAtoms : M Expr
  /--
  A cache for `toExpr bvExpr`
  -/
  expr : Expr


namespace M

/--
Run a reflection computation as a `MetaM` one.
-/
def run (m : M α) : MetaM α :=
  m.run' { }

/--
Retrieve the atoms as pairs of their width and expression.
-/
def atoms : M (Array (Nat × Expr)) := do
  let sortedAtoms := (← getThe State).atoms.toArray.qsort (·.2.atomNumber < ·.2.atomNumber)
  return sortedAtoms.map (fun (expr, {width, ..}) => (width, expr))

/--
Retrieve a `BitVec.Assignment` representing the atoms we found so far.
-/
def atomsAssignment : M Expr := do
  match (← getThe State).atomsAssignmentCache with
  | some cache => return cache
  | none => updateAtomsAssignment
where
  updateAtomsAssignment : M Expr := do
    let as ← atoms
    if h : 0 < as.size then
      let ras := Lean.RArray.ofArray as h
      let packedType := mkConst ``BVExpr.PackedBitVec
      let pack := fun (width, expr) => mkApp2 (mkConst ``BVExpr.PackedBitVec.mk) (toExpr width) expr
      let newAtomsAssignment := ras.toExpr packedType pack
      modify fun s => { s with atomsAssignmentCache := some newAtomsAssignment }
      return newAtomsAssignment
    else
      throwError "updateAtomsAssignment should only be called when there is an atom"

/--
Look up an expression in the atoms, recording it if it has not previously appeared.
-/
def lookup (e : Expr) (width : Nat) (synthetic : Bool) : M Nat := do
  match (← getThe State).atoms[e]? with
  | some atom =>
    if width != atom.width then
      panic! "The same atom occurs with different widths, this is a bug"
    return atom.atomNumber
  | none =>
    trace[Meta.Tactic.bv] "New atom of width {width}, synthetic? {synthetic}: {e}"
    let ident ← modifyGetThe State fun s =>
      let newAtom := { width, synthetic, atomNumber := s.atoms.size}
      let newAtomNumber := s.atoms.size
      let s := {
        s with
          atoms := s.atoms.insert e newAtom,
          -- must clear the caches as they depend on `atoms`.
          atomsAssignmentCache := none
          evalsAtCache := {}
      }
      (newAtomNumber, s)
    return ident

@[specialize]
def simplifyBinaryProof' (mkFRefl : Expr → Expr) (fst : Expr) (fproof : Option Expr)
    (mkSRefl : Expr → Expr) (snd : Expr) (sproof : Option Expr) : Option (Expr × Expr) := do
  match fproof, sproof with
  | some fproof, some sproof => some (fproof, sproof)
  | some fproof, none => some (fproof, mkSRefl snd)
  | none, some sproof => some (mkFRefl fst, sproof)
  | none, none => none

@[specialize]
def simplifyBinaryProof (mkRefl : Expr → Expr) (fst : Expr) (fproof : Option Expr) (snd : Expr)
    (sproof : Option Expr) : Option (Expr × Expr) := do
  simplifyBinaryProof' mkRefl fst fproof mkRefl snd sproof

@[specialize]
def simplifyTernaryProof (mkRefl : Expr → Expr) (fst : Expr) (fproof : Option Expr) (snd : Expr)
    (sproof : Option Expr) (thd : Expr) (tproof : Option Expr) : Option (Expr × Expr × Expr) := do
  match fproof, simplifyBinaryProof mkRefl snd sproof thd tproof with
  | some fproof, some stproof => some (fproof, stproof)
  | some fproof, none => some (fproof, mkRefl snd, mkRefl thd)
  | none, some stproof => some (mkRefl fst, stproof)
  | none, none => none

end M

/--
The state of the lemma reflection monad.
-/
structure LemmaState where
  /--
  The list of top level lemmas that got created on the fly during reflection.
  -/
  lemmas : Array SatAtBVLogical := #[]
  /--
  Cache for reification of `BVExpr`.
  -/
  bvExprCache : Std.HashMap Expr (Option ReifiedBVExpr) := {}
  /--
  Cache for reification of `BVPred`.
  -/
  bvPredCache : Std.HashMap Expr (Option ReifiedBVPred) := {}
  /--
  Cache for reification of `BVLogicalExpr`.
  -/
  bvLogicalCache : Std.HashMap Expr (Option ReifiedBVLogical) := {}

/--
The lemma reflection monad. It extends the usual reflection monad `M` by adding the ability to
add additional top level lemmas on the fly.
-/
abbrev LemmaM := StateRefT LemmaState M

namespace LemmaM

def run (m : LemmaM α) (state : LemmaState := {}) : M (α × Array SatAtBVLogical) := do
  let (res, state) ← StateRefT'.run m state
  return (res, state.lemmas)

/--
Add another top level lemma.
-/
def addLemma (lemma : SatAtBVLogical) : LemmaM Unit := do
  modify fun s => { s with lemmas := s.lemmas.push lemma }

@[specialize]
def withBVExprCache (e : Expr) (f : Expr → LemmaM (Option ReifiedBVExpr)) :
    LemmaM (Option ReifiedBVExpr) := do
  match (← get).bvExprCache[e]? with
  | some hit => return hit
  | none =>
    let res ← f e
    modify fun s => { s with bvExprCache := s.bvExprCache.insert e res }
    return res

@[specialize]
def withBVPredCache (e : Expr) (f : Expr → LemmaM (Option ReifiedBVPred)) :
    LemmaM (Option ReifiedBVPred) := do
  match (← get).bvPredCache[e]? with
  | some hit => return hit
  | none =>
    let res ← f e
    modify fun s => { s with bvPredCache := s.bvPredCache.insert e res }
    return res

@[specialize]
def withBVLogicalCache (e : Expr) (f : Expr → LemmaM (Option ReifiedBVLogical)) :
    LemmaM (Option ReifiedBVLogical) := do
  match (← get).bvLogicalCache[e]? with
  | some hit => return hit
  | none =>
    let res ← f e
    modify fun s => { s with bvLogicalCache := s.bvLogicalCache.insert e res }
    return res

end LemmaM

end Frontend
end Lean.Elab.Tactic.BVDecide
