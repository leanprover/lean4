/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Grind.Arith.EvalNum
import Lean.Meta.Tactic.Grind.SynthInstance

namespace Lean.Meta.Grind.Arith

def getIsCharInst? (u : Level) (type : Expr) (semiringInst : Expr) : GoalM (Option (Expr × Nat)) := do withNewMCtxDepth do
  let n ← mkFreshExprMVar (mkConst ``Nat)
  let charType := mkApp3 (mkConst ``Grind.IsCharP [u]) type semiringInst n
  let some charInst ← synthInstance? charType | return none
  let n ← instantiateMVars n
  let some n ← evalNat? n | return none
  return some (charInst, n)

def getNoZeroDivInst? (u : Level) (type : Expr) : GoalM (Option Expr) := do
  let hmulType := mkApp3 (mkConst ``HMul [0, u, u]) (mkConst ``Nat []) type type
  let some hmulInst ← synthInstance? hmulType | return none
  let noZeroDivType := mkApp2 (mkConst ``Grind.NoNatZeroDivisors [u]) type hmulInst
  synthInstance? noZeroDivType

end Lean.Meta.Grind.Arith
