import Lean.Meta.Sym
open Lean Meta Sym

/-!
A failed `BackwardRule.apply` must not leave metavariable assignments behind, as `MVarId.apply`
restores the state of each failed attempt. Callers such as VCGen try several rules on the same goal.
The tests use the `SymM` API: in `sym =>` scripts, a failed `apply` throws, and the combinators
(`first`, `try`, ...) restore the saved state.
-/

theorem r (a : Nat) : a + 1 = 0 → a + 1 = 0 := id

/-- Unification assigns `?w := ?a + 1`, then fails on `?a + 1 =?= 0`. -/
def testUnifyFailure : SymM Unit := do
  let rule ← mkBackwardRuleFromDecl ``r
  let w ← mkFreshExprMVar (mkConst ``Nat)
  let mvarId ← preprocessMVar (← mkFreshExprMVar (← mkEq w w)).mvarId!
  let .failed ← rule.apply mvarId | throwError "unexpected success"
  logInfo m!"{← instantiateMVars w}"

/-- info: ?m.1 -/
#guard_msgs in
#eval SymM.run testUnifyFailure

class C (α : Type) where
  val : α

theorem s [C Nat] (a : Nat) : a + 1 = a + 1 := rfl

/-- Unification assigns `?w := ?a + 1`, then `apply` fails because `C Nat` cannot be synthesized. -/
def testUnresolvedInst : SymM Unit := do
  let rule ← mkBackwardRuleFromDecl ``s
  let w ← mkFreshExprMVar (mkConst ``Nat)
  let mvarId ← preprocessMVar (← mkFreshExprMVar (← mkEq w w)).mvarId!
  let .failed ← rule.apply mvarId | throwError "unexpected success"
  logInfo m!"{← instantiateMVars w}"

/-- info: ?m.1 -/
#guard_msgs in
#eval SymM.run testUnresolvedInst
