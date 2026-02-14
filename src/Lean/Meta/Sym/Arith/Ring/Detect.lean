/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Sym.Arith.Ring.SymExt
import Lean.Meta.SynthInstance
import Lean.Meta.DecLevel
public section
namespace Lean.Meta.Sym.Arith.Ring

/--
Wrapper around `Meta.synthInstance?` that catches `isDefEqStuck` exceptions
(which can occur when instance arguments contain metavariables or are not in normal form).
-/
private def synthInstance? (type : Expr) : SymM (Option Expr) :=
  catchInternalId isDefEqStuckExceptionId
    (Meta.synthInstance? type)
    (fun _ => pure none)

/--
Evaluate a `Nat`-typed expression to a concrete `Nat` value.
Handles `OfNat.ofNat`, `HPow.hPow`, `HAdd.hAdd`, `HMul.hMul`, `HSub.hSub`,
`Nat.zero`, `Nat.succ`, and raw `Nat` literals.
This is simpler than `Grind.Arith.evalNat?` (no threshold checks, no `Int` support)
but sufficient for evaluating `IsCharP` characteristic values like `2^8`.
-/
private partial def evalNat? (e : Expr) : Option Nat :=
  match_expr e with
  | OfNat.ofNat _ n _ =>
    match n with
    | .lit (.natVal k) => some k
    | _ => evalNat? n
  | Nat.zero => some 0
  | Nat.succ a => (· + 1) <$> evalNat? a
  | HAdd.hAdd _ _ _ _ a b => (· + ·) <$> evalNat? a <*> evalNat? b
  | HMul.hMul _ _ _ _ a b => (· * ·) <$> evalNat? a <*> evalNat? b
  | HSub.hSub _ _ _ _ a b => (· - ·) <$> evalNat? a <*> evalNat? b
  | HPow.hPow _ _ _ _ a b => (· ^ ·) <$> evalNat? a <*> evalNat? b
  | _ =>
    match e with
    | .lit (.natVal k) => some k
    | _ => none

/--
Detect whether `type` has a `Grind.CommRing` instance.
Returns the shared ring id if found. The `CommRing` object is stored in
`arithRingExt` and is shared between `Sym.simp` and `grind`.
Results are cached in `arithRingExt.typeIdOf`.
-/
def detectCommRing? (type : Expr) : SymM (Option Nat) := do
  let s ← arithRingExt.getState
  if let some id? := s.typeIdOf.find? { expr := type } then
    return id?
  let some ring ← go? | do
    arithRingExt.modifyState fun st => { st with typeIdOf := st.typeIdOf.insert { expr := type } none }
    return none
  let id := s.rings.size
  let ring := { ring with toRing.id := id }
  arithRingExt.modifyState fun st => { st with
    rings := st.rings.push ring
    typeIdOf := st.typeIdOf.insert { expr := type } (some id)
  }
  return some id
where
  go? : SymM (Option CommRing) := do
    let u ← getDecLevel type
    let commRing := mkApp (mkConst ``Grind.CommRing [u]) type
    let some commRingInst ← synthInstance? commRing | return none
    let ringInst := mkApp2 (mkConst ``Grind.CommRing.toRing [u]) type commRingInst
    let semiringInst := mkApp2 (mkConst ``Grind.Ring.toSemiring [u]) type ringInst
    let commSemiringInst := mkApp2 (mkConst ``Grind.CommRing.toCommSemiring [u]) type semiringInst
    let charInst? ← getIsCharInst? u type semiringInst
    let noZeroDivInst? ← getNoZeroDivInst? u type
    let fieldInst? ← synthInstance? <| mkApp (mkConst ``Grind.Field [u]) type
    return some {
      id := 0, type, u, semiringInst, ringInst, commSemiringInst,
      commRingInst, charInst?, noZeroDivInst?, fieldInst?,
      semiringId? := none,
    }

  getIsCharInst? (u : Level) (type : Expr) (semiringInst : Expr) : SymM (Option (Expr × Nat)) := do
    withNewMCtxDepth do
      let n ← mkFreshExprMVar (mkConst ``Nat)
      let charType := mkApp3 (mkConst ``Grind.IsCharP [u]) type semiringInst n
      let some charInst ← synthInstance? charType | return none
      let n ← instantiateMVars n
      let some nVal := evalNat? n | return none
      return some (charInst, nVal)

  getNoZeroDivInst? (u : Level) (type : Expr) : SymM (Option Expr) := do
    let natModuleType := mkApp (mkConst ``Grind.NatModule [u]) type
    let some natModuleInst ← synthInstance? natModuleType | return none
    let noZeroDivType := mkApp2 (mkConst ``Grind.NoNatZeroDivisors [u]) type natModuleInst
    synthInstance? noZeroDivType

end Lean.Meta.Sym.Arith.Ring
