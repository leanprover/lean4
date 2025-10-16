import Lean

run_meta
  Lean.Meta.mkSparseCasesOn ``Lean.Expr #[``Lean.Expr.fvar, ``Lean.Expr.sort] `justATest

#with_exporting
#print justATest
