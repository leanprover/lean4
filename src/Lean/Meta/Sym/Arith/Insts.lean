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

end Lean.Meta.Sym.Arith
