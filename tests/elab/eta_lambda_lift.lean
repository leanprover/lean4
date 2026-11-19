import Lean.Util.FindExpr

/-!
This test asserts that the compiler will eta contract trivial lambdas instead of lambda lifting
them.
-/

/--
trace: [Compiler.lambdaLifting] size: 2
    def test e : Option Lean.Expr :=
      let _f.1 := Lean.Expr.hasMVar;
      let _x.2 := Lean.Expr.findImpl? _f.1 e;
      return _x.2
-/
#guard_msgs in
set_option trace.Compiler.lambdaLifting true in
def test (e : Lean.Expr) := e.find? (fun e => e.hasMVar)
