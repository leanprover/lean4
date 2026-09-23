/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Sym.Arith.EvalNum
import Lean.Meta.Sym.SynthInstance
import Init.Grind.Ring
public section

namespace Lean.Meta.Sym.Arith

/-!
Helpers for synthesizing the optional instances attached to a classified ring:
`IsCharP`, `PowIdentity`, and `NoNatZeroDivisors`.
-/

/-- Returns the `IsCharP type semiringInst n` instance together with the evaluated `n`. -/
def getIsCharInst? (u : Level) (type : Expr) (semiringInst : Expr) : SymM (Option (Expr × Nat)) := withNewMCtxDepth do
  let n ← mkFreshExprMVar (mkConst ``Nat)
  let charType := mkApp3 (mkConst ``Grind.IsCharP [u]) type semiringInst n
  let some charInst ← synthInstance? charType | return none
  let n ← instantiateMVars n
  let some n ← evalNat? n | return none
  return some (charInst, n)

/--
Returns the `PowIdentity` instance, the `CommSemiring` instance it was synthesized against,
and the evaluated exponent `p`.
-/
def getPowIdentityInst? (u : Level) (type : Expr) : SymM (Option (Expr × Expr × Nat)) := withNewMCtxDepth do
  -- We use a fresh metavar for `CommSemiring` (unlike `getIsCharInst?` which pins the semiring)
  -- because `PowIdentity` instances may be declared against a canonical `CommSemiring` instance
  -- that is not definitionally equal to `CommRing.toCommSemiring`. The synthesized `csInst` is
  -- stored and used in proof terms to ensure type-correctness.
  let csInst ← mkFreshExprMVar (mkApp (mkConst ``Grind.CommSemiring [u]) type)
  let p ← mkFreshExprMVar (mkConst ``Nat)
  let powIdentityType := mkApp3 (mkConst ``Grind.PowIdentity [u]) type csInst p
  let some inst ← synthInstance? powIdentityType | return none
  let csInst ← instantiateMVars csInst
  let p ← instantiateMVars p
  let some pVal ← evalNat? p | return none
  return some (inst, csInst, pVal)

/-- Returns the `NoNatZeroDivisors` instance for `type`, synthesizing the `NatModule` premise first. -/
def getNoZeroDivInst? (u : Level) (type : Expr) : SymM (Option Expr) := do
  let natModuleType := mkApp (mkConst ``Grind.NatModule [u]) type
  let some natModuleInst ← synthInstance? natModuleType | return none
  let noZeroDivType := mkApp2 (mkConst ``Grind.NoNatZeroDivisors [u]) type natModuleInst
  synthInstance? noZeroDivType

/-! Order instances. Each returns `none` (with a debug issue) when `synthInstance?` fails. -/

def mkLawfulOrderLTInst? (u : Level) (type : Expr) (ltInst? leInst? : Option Expr) : SymM (Option Expr) := do
  let some ltInst := ltInst? | return none
  let some leInst := leInst? | return none
  let lawfulOrderLTType := mkApp3 (mkConst ``Std.LawfulOrderLT [u]) type ltInst leInst
  let some inst ← synthInstance? lawfulOrderLTType
    | reportDbgIssue! "type has `LE` and `LT`, but the `LT` instance is not lawful, failed to synthesize{indentExpr lawfulOrderLTType}"
      return none
  return some inst

def mkIsPreorderInst? (u : Level) (type : Expr) (leInst? : Option Expr) : SymM (Option Expr) := do
  let some leInst := leInst? | return none
  let isPreorderType := mkApp2 (mkConst ``Std.IsPreorder [u]) type leInst
  let some inst ← synthInstance? isPreorderType
    | reportDbgIssue! "type has `LE`, but is not a preorder, failed to synthesize{indentExpr isPreorderType}"
      return none
  return some inst

def mkIsPartialOrderInst? (u : Level) (type : Expr) (leInst? : Option Expr) : SymM (Option Expr) := do
  let some leInst := leInst? | return none
  let isPartialOrderType := mkApp2 (mkConst ``Std.IsPartialOrder [u]) type leInst
  let some inst ← synthInstance? isPartialOrderType
    | reportDbgIssue! "type has `LE`, but is not a partial order, failed to synthesize{indentExpr isPartialOrderType}"
      return none
  return some inst

def mkIsLinearOrderInst? (u : Level) (type : Expr) (leInst?  : Option Expr) : SymM (Option Expr) := do
  let some leInst := leInst? | return none
  let isLinearOrderType := mkApp2 (mkConst ``Std.IsLinearOrder [u]) type leInst
  let some inst ← synthInstance? isLinearOrderType
    | reportDbgIssue! "type has `LE`, but is not a linear order, failed to synthesize{indentExpr isLinearOrderType}"
      return none
  return some inst

def mkIsLinearPreorderInst? (u : Level) (type : Expr) (leInst?  : Option Expr) : SymM (Option Expr) := do
  let some leInst := leInst? | return none
  let isLinearOrderType := mkApp2 (mkConst ``Std.IsLinearPreorder [u]) type leInst
  let some inst ← synthInstance? isLinearOrderType
    | reportDbgIssue! "type has `LE`, but is not a linear preorder, failed to synthesize{indentExpr isLinearOrderType}"
      return none
  return some inst

end Lean.Meta.Sym.Arith
