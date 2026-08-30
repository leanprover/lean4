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

/-!
The following example used to have the following error on 'example' due to creating a type-incorrect term:
```
application type mismatch
  { t := Type }
argument has type
  Type 1
but function has type
  Type v → S
```
-/

structure S.{u} where
  t : Type u

-- this error is on the first 'exact'
/--
error: type mismatch
  m
has type
  S.t ?m : Type v
but is expected to have type
  Type : Type 1
-/
#guard_msgs in
example (α : Type v) : Type := by
  have m : (?m : S.{v}).t := ?n
  exact m -- 'assumption' worked too
  exact Nat
