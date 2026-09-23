/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Sym.Arith.Insts
import Lean.Meta.Sym.SynthInstance
import Lean.Meta.Sym.Canon
import Lean.Meta.DecLevel
import Init.Grind.Ring
public section

namespace Lean.Meta.Sym.Arith

/-!
# Algebraic structure classification

Detects the strongest algebraic structure available for a type and caches
the classification in `Arith.State.typeClassify`. The state is a `SymExtension`,
so a type is classified once per `SymM` run and the result is shared by every
`grind` goal and every tactic of a `sym` block. The detection order is:

1. `Grind.CommRing` (includes `Field` check)
2. `Grind.Ring` (non-commutative)
3. `Grind.CommSemiring` (via `OfSemiring.Q` envelope)
4. `Grind.Semiring` (non-commutative)

Results (including failures) are cached in a single `PHashMap ExprPtr ClassifyResult`
to avoid repeated synthesis attempts.
-/

/--
Fast path for the envelope type `Ring.OfSemiring.Q base` where `semiringInst` is
`CommSemiring.toSemiring base commSemiringInst`. Synthesizing instances for the envelope is
very expensive in Mathlib, so we construct them by hand and register them with
`registerInstance`, which makes `synthInstance?` (and hence `canon`) return them directly.
-/
private def tryCommRingQ? (type base semiringInst commSemiringInst : Expr) : SymM (Option Nat) := do
  let some u ← getDecLevel? base | return none
  let commRingInst := mkApp2 (mkConst ``Grind.CommRing.OfCommSemiring.ofCommSemiring [u]) base commSemiringInst
  let ringInst := mkApp2 (mkConst ``Grind.CommRing.toRing [u]) type commRingInst
  let semiringInstQ := mkApp2 (mkConst ``Grind.Ring.toSemiring [u]) type ringInst
  let commSemiringInstQ := mkApp2 (mkConst ``Grind.CommRing.toCommSemiring [u]) type semiringInstQ
  registerInstance (mkApp (mkConst ``Grind.CommRing [u]) type) commRingInst
  registerInstance (mkApp (mkConst ``Grind.Ring [u]) type) ringInst
  registerInstance (mkApp (mkConst ``Grind.Semiring [u]) type) semiringInstQ
  registerInstance (mkApp (mkConst ``Grind.CommSemiring [u]) type) commSemiringInstQ
  registerInstance (mkApp (mkConst ``Grind.NatModule [u]) type)
    (mkApp2 (mkConst ``Grind.Semiring.toNatModule [u]) type semiringInstQ)
  registerInstance (mkApp3 (mkConst ``HAdd [u, u, u]) type type type)
    (mkApp2 (mkConst ``instHAdd [u]) type (mkApp2 (mkConst ``Grind.Semiring.toAdd [u]) type semiringInstQ))
  registerInstance (mkApp3 (mkConst ``HMul [u, u, u]) type type type)
    (mkApp2 (mkConst ``instHMul [u]) type (mkApp2 (mkConst ``Grind.Semiring.toMul [u]) type semiringInstQ))
  registerInstance (mkApp3 (mkConst ``HSub [u, u, u]) type type type)
    (mkApp2 (mkConst ``instHSub [u]) type (mkApp2 (mkConst ``Grind.Ring.toSub [u]) type ringInst))
  registerInstance (mkApp (mkConst ``Neg [u]) type)
    (mkApp2 (mkConst ``Grind.Ring.toNeg [u]) type ringInst)
  registerInstance (mkApp3 (mkConst ``HPow [u, 0, u]) type Nat.mkType type)
    (mkApp2 (mkConst ``Grind.Semiring.npow [u]) type semiringInstQ)
  registerInstance (mkApp (mkConst ``NatCast [u]) type)
    (mkApp2 (mkConst ``Grind.Semiring.natCast [u]) type semiringInstQ)
  registerInstance (mkApp (mkConst ``IntCast [u]) type)
    (mkApp2 (mkConst ``Grind.Ring.intCast [u]) type ringInst)
  trace[grind.ring] "new ring: {type}"
  -- Premises on the base type for the conditional envelope instances.
  let addRightCancelInst? ← do
    let some addInst ← synthInstance? (mkApp (mkConst ``Add [u]) base) | pure none
    synthInstance? (mkApp2 (mkConst ``Grind.AddRightCancel [u]) base addInst)
  let charInst? ← do
    let some addRightCancelInst := addRightCancelInst? | pure none
    let some (baseCharInst, n) ← getIsCharInst? u base semiringInst | pure none
    let inst := mkApp5 (mkConst ``Grind.Ring.OfSemiring.instIsCharPQOfAddRightCancel [u])
      base (mkRawNatLit n) semiringInst addRightCancelInst baseCharInst
    pure (some (inst, n))
  let noZeroDivInst? ← do
    let some addRightCancelInst := addRightCancelInst? | pure none
    -- `getNoZeroDivInst?` synthesizes the `NatModule base` premise instead of using
    -- `Semiring.toNatModule`, so this query is shared with the one issued for the
    -- `IntModule.OfNatModule.Q base` envelope; the results are definitionally equal.
    let some noZeroDivInst ← getNoZeroDivInst? u base | pure none
    pure (some (mkApp4 (mkConst ``Grind.Ring.OfSemiring.instNoNatZeroDivisorsQOfAddRightCancel [u])
      base semiringInst addRightCancelInst noZeroDivInst))
  trace[grind.ring] "NoNatZeroDivisors available: {noZeroDivInst?.isSome}"
  trace[grind.ring] "PowIdentity available: false"
  let id := (← getArithState).rings.size
  let ring : CommRing := {
    id, semiringId? := none, type, u, semiringInst := semiringInstQ, ringInst,
    commSemiringInst := commSemiringInstQ,
    commRingInst, charInst?, noZeroDivInst?, fieldInst? := none, powIdentityInst? := none,
  }
  modifyArithState fun s => { s with rings := s.rings.push ring }
  return some id

private def tryCommRingCore? (type : Expr) : SymM (Option Nat) := do
  let u ← getDecLevel type
  let commRing := mkApp (mkConst ``Grind.CommRing [u]) type
  let some commRingInst ← Sym.synthInstance? commRing | return none
  let ringInst := mkApp2 (mkConst ``Grind.CommRing.toRing [u]) type commRingInst
  let semiringInst := mkApp2 (mkConst ``Grind.Ring.toSemiring [u]) type ringInst
  let commSemiringInst := mkApp2 (mkConst ``Grind.CommRing.toCommSemiring [u]) type semiringInst
  trace[grind.ring] "new ring: {type}"
  let charInst? ← getIsCharInst? u type semiringInst
  let noZeroDivInst? ← getNoZeroDivInst? u type
  trace[grind.ring] "NoNatZeroDivisors available: {noZeroDivInst?.isSome}"
  let fieldInst? ← Sym.synthInstance? <| mkApp (mkConst ``Grind.Field [u]) type
  let powIdentityInst? ← getPowIdentityInst? u type
  trace[grind.ring] "PowIdentity available: {powIdentityInst?.isSome}"
  let semiringId? := none
  let id := (← getArithState).rings.size
  let ring : CommRing := {
    id, semiringId?, type, u, semiringInst, ringInst, commSemiringInst,
    commRingInst, charInst?, noZeroDivInst?, fieldInst?, powIdentityInst?,
  }
  modifyArithState fun s => { s with rings := s.rings.push ring }
  return some id

/-- Try to classify `type` as a `CommRing`. Returns the ring id on success. -/
private def tryCommRing? (type : Expr) : SymM (Option Nat) := do
  let_expr Grind.Ring.OfSemiring.Q base semiringInst := type | tryCommRingCore? type
  -- `tryCommSemiring?` instantiates the envelope with `CommSemiring.toSemiring`;
  -- fall back to the generic path otherwise.
  let_expr Grind.CommSemiring.toSemiring _ commSemiringInst := semiringInst | tryCommRingCore? type
  tryCommRingQ? type base semiringInst commSemiringInst

/-- Try to classify `type` as a non-commutative `Ring`. -/
private def tryNonCommRing? (type : Expr) : SymM (Option Nat) := do
  let u ← getDecLevel type
  let ring := mkApp (mkConst ``Grind.Ring [u]) type
  let some ringInst ← Sym.synthInstance? ring | return none
  let semiringInst := mkApp2 (mkConst ``Grind.Ring.toSemiring [u]) type ringInst
  trace[grind.ring] "new ring: {type}"
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

private def canonFn (fn : Expr) : SymM Expr := do
  shareCommon (← Sym.canon fn)

private def mkOrderedRingInst? (u : Level) (type : Expr) (semiringInst : Expr)
    (leInst ltInst isPreorderInst : Expr) : SymM (Option Expr) := do
  synthInstance? <| mkApp5 (mkConst ``Grind.OrderedRing [u]) type semiringInst leInst ltInst isPreorderInst

private def tryOrder? (type : Expr) : SymM (Option Nat) := do
  let some u ← getDecLevel? type | return none
  let some leInst ← synthInstance? (mkApp (mkConst ``LE [u]) type) | return none
  let some isPreorderInst ← mkIsPreorderInst? u type (some leInst) | return none
  let isPartialInst? ← mkIsPartialOrderInst? u type (some leInst)
  let isLinearPreInst? ← mkIsLinearPreorderInst? u type (some leInst)
  let ltInst? ← synthInstance? (mkApp (mkConst ``LT [u]) type)
  let leFn ← canonFn <| mkApp2 (mkConst ``LE.le [u]) type leInst
  let (lawfulOrderLTInst?, ltFn?) ← if let some ltInst := ltInst? then
    let inst? ← mkLawfulOrderLTInst? u type ltInst? (some leInst)
    if inst?.isNone then
      pure (none, none)
    else
      pure (inst?, some (← canonFn <| mkApp2 (mkConst ``LT.lt [u]) type ltInst))
  else
    pure (none, none)
  -- The ring link is only used by `grind order` for offsets, which need `<`.
  let (ringId?, ringInst?, orderedRingInst?, isCommRing) ← if lawfulOrderLTInst?.isNone then
    pure (none, none, none, false)
  else match (← classify? type) with
    | .commRing ringId =>
      let ring := (← getArithState).rings[ringId]!
      let some ordRingInst ← mkOrderedRingInst? u type ring.semiringInst leInst ltInst?.get! isPreorderInst
        | pure (none, none, none, true)
      pure (some ringId, some ring.ringInst, some ordRingInst, true)
    | .nonCommRing ringId =>
      let ring := (← getArithState).ncRings[ringId]!
      let some ordRingInst ← mkOrderedRingInst? u type ring.semiringInst leInst ltInst?.get! isPreorderInst
        | pure (none, none, none, false)
      pure (some ringId, some ring.ringInst, some ordRingInst, false)
    | _ => pure (none, none, none, false)
  let id := (← getArithState).orders.size
  let order : Order := {
    id, type, u, leInst, isPreorderInst, ltInst?, leFn, isPartialInst?, ringInst?, orderedRingInst?
    isLinearPreInst?, ltFn?, lawfulOrderLTInst?, ringId?, isCommRing
  }
  modifyArithState fun s => { s with orders := s.orders.push order }
  return some id

/--
Classify `type` as an order structure (at least `IsPreorder`), returning its id in
`State.orders`. Results, including failures, are cached in `State.typeOrderClassify`.
-/
def classifyOrder? (type : Expr) : SymM (Option Nat) := do
  if let some id? := (← getArithState).typeOrderClassify.find? { expr := type } then
    return id?
  let id? ← tryOrder? type
  modifyArithState fun s => { s with typeOrderClassify := s.typeOrderClassify.insert { expr := type } id? }
  return id?

end Lean.Meta.Sym.Arith
