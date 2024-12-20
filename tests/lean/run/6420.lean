import Lean
/-!
# Testing fix to `isDefEqSingleton`
https://github.com/leanprover/lean4/issues/6420
-/

/-!
The following example used to print `unifiable? true`.
-/
open Lean

structure foo where
  bar : Nat

/-- info: unifiable? false -/
#guard_msgs in
#eval show MetaM Unit from do
  let lhs := Expr.const ``foo []
  let m ← Meta.mkFreshExprMVar lhs
  let rhs := Expr.app (.const ``foo.bar []) m
  let defeq? ← Meta.isDefEq lhs rhs
  logInfo m!"unifiable? {defeq?}"
