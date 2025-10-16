import Lean

run_meta
  Lean.Meta.mkSparseCasesOn ``Lean.Expr #[``Lean.Expr.fvar, ``Lean.Expr.sort] `justATest

/--
info: justATest.{u} {motive : Lean.Expr → Sort u} (t : Lean.Expr)
  (fvar : (fvarId : Lean.FVarId) → motive (Lean.Expr.fvar fvarId)) (sort : (u : Lean.Level) → motive (Lean.Expr.sort u))
  («else» : (t : Lean.Expr) → t.ctorIdx ≠ 1 → t.ctorIdx ≠ 3 → motive t) : motive t
-/
#guard_msgs in
#check justATest
