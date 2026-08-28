/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Sym.Arith.EvalNum
import Lean.Meta.Sym.SynthInstance
import Lean.Meta.Sym.Canon
import Lean.Meta.DecLevel
import Init.Grind.Ring
public section

namespace Lean.Meta.Sym.Arith

/-!
# Algebraic structure classification

Detects the strongest algebraic structure available for a type and caches
the classification in `Arith.State.typeClassify`. The detection order is:

1. `Grind.CommRing` (includes `Field` check)
2. `Grind.Ring` (non-commutative)
3. `Grind.CommSemiring` (via `OfSemiring.Q` envelope)
4. `Grind.Semiring` (non-commutative)

Results (including failures) are cached in a single `PHashMap ExprPtr ClassifyResult`
to avoid repeated synthesis attempts.
-/

private def getIsCharInst? (u : Level) (type : Expr) (semiringInst : Expr) : SymM (Option (Expr × Nat)) := do
  withNewMCtxDepth do
    let n ← mkFreshExprMVar (mkConst ``Nat)
    let charType := mkApp3 (mkConst ``Grind.IsCharP [u]) type semiringInst n
    let some charInst ← Sym.synthInstance? charType | return none
    let n ← instantiateMVars n
    let some n ← evalNat? n | return none
    return some (charInst, n)

private def getNoZeroDivInst? (u : Level) (type : Expr) : SymM (Option Expr) := do
  let natModuleType := mkApp (mkConst ``Grind.NatModule [u]) type
  let some natModuleInst ← Sym.synthInstance? natModuleType | return none
  let noZeroDivType := mkApp2 (mkConst ``Grind.NoNatZeroDivisors [u]) type natModuleInst
  Sym.synthInstance? noZeroDivType

/-- Try to classify `type` as a `CommRing`. Returns the ring id on success. -/
private def tryCommRing? (type : Expr) : SymM (Option Nat) := do
  let u ← getDecLevel type
  let commRing := mkApp (mkConst ``Grind.CommRing [u]) type
  let some commRingInst ← Sym.synthInstance? commRing | return none
  let ringInst := mkApp2 (mkConst ``Grind.CommRing.toRing [u]) type commRingInst
  let semiringInst := mkApp2 (mkConst ``Grind.Ring.toSemiring [u]) type ringInst
  let commSemiringInst := mkApp2 (mkConst ``Grind.CommRing.toCommSemiring [u]) type semiringInst
  let charInst? ← getIsCharInst? u type semiringInst
  let noZeroDivInst? ← getNoZeroDivInst? u type
  let fieldInst? ← Sym.synthInstance? <| mkApp (mkConst ``Grind.Field [u]) type
  let semiringId? := none
  let id := (← getArithState).rings.size
  let ring : CommRing := {
    id, semiringId?, type, u, semiringInst, ringInst, commSemiringInst,
    commRingInst, charInst?, noZeroDivInst?, fieldInst?,
  }
  modifyArithState fun s => { s with rings := s.rings.push ring }
  return some id

/-- Try to classify `type` as a non-commutative `Ring`. -/
private def tryNonCommRing? (type : Expr) : SymM (Option Nat) := do
  let u ← getDecLevel type
  let ring := mkApp (mkConst ``Grind.Ring [u]) type
  let some ringInst ← Sym.synthInstance? ring | return none
  let semiringInst := mkApp2 (mkConst ``Grind.Ring.toSemiring [u]) type ringInst
  let charInst? ← getIsCharInst? u type semiringInst
  let id := (← getArithState).ncRings.size
  let ring : Ring := {
    id, type, u, semiringInst, ringInst, charInst?
  }
  modifyArithState fun s => { s with ncRings := s.ncRings.push ring }
  return some id

/-- Helper function for `tryCommSemiring? -/
private def tryCacheAndCommRing? (type : Expr) : SymM (Option Nat) := do
  if let some result := (← getArithState).typeClassify.find? { expr := type } then
    let .commRing id := result | return none
    return id
  let id? ← tryCommRing? type
  let result := match id? with
    | none => .none
    | some id => .commRing id
  modifyArithState fun s => { s with typeClassify := s.typeClassify.insert { expr := type } result }
  return id?

/-- Try to classify `type` as a `CommSemiring`. Creates the `OfSemiring.Q` envelope ring. -/
private def tryCommSemiring? (type : Expr) : SymM (Option Nat) := do
  let u ← getDecLevel type
  let commSemiring := mkApp (mkConst ``Grind.CommSemiring [u]) type
  let some commSemiringInst ← Sym.synthInstance? commSemiring | return none
  let semiringInst := mkApp2 (mkConst ``Grind.CommSemiring.toSemiring [u]) type commSemiringInst
  let q ← shareCommon (← Sym.canon (mkApp2 (mkConst ``Grind.Ring.OfSemiring.Q [u]) type semiringInst))
  -- The envelope `Q` type must be classifiable as a CommRing.
  let some ringId ← tryCacheAndCommRing? q
    | reportIssue! "unexpected failure initializing ring{indentExpr q}"; return none
  let id := (← getArithState).semirings.size
  let semiring : CommSemiring := {
    id, type, ringId, u, semiringInst, commSemiringInst
  }
  modifyArithState fun s => { s with semirings := s.semirings.push semiring }
  -- Link the envelope ring back to this semiring
  modifyArithState fun s =>
    let rings := s.rings.modify ringId fun r => { r with semiringId? := some id }
    { s with rings }
  return some id

/-- Try to classify `type` as a non-commutative `Semiring`. -/
private def tryNonCommSemiring? (type : Expr) : SymM (Option Nat) := do
  let u ← getDecLevel type
  let semiring := mkApp (mkConst ``Grind.Semiring [u]) type
  let some semiringInst ← Sym.synthInstance? semiring | return none
  let id := (← getArithState).ncSemirings.size
  let semiring : Semiring := { id, type, u, semiringInst }
  modifyArithState fun s => { s with ncSemirings := s.ncSemirings.push semiring }
  return some id

/--
Classify the algebraic structure of `type`, trying the strongest first:
CommRing > Ring > CommSemiring > Semiring.
Results are cached in `Arith.State.typeClassify`.
-/
def classify? (type : Expr) : SymM ClassifyResult := do
  if let some result := (← getArithState).typeClassify.find? { expr := type } then
    return result
  let result ← go
  modifyArithState fun s => { s with typeClassify := s.typeClassify.insert { expr := type } result }
  return result
where
  go : SymM ClassifyResult := do
    if let some id ← tryCommRing? type then return .commRing id
    if let some id ← tryNonCommRing? type then return .nonCommRing id
    if let some id ← tryCommSemiring? type then return .commSemiring id
    if let some id ← tryNonCommSemiring? type then return .nonCommSemiring id
    return .none

end Lean.Meta.Sym.Arith
