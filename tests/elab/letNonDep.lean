import Lean
/-!
# Tests of `Expr.letE (nondep := true) ..`

This file exercises the Lean/C++ interface to make sure that the `nondep` field
is successfully part of the data model.

It also tests the metaprogramming API.
-/

open Lean

/-!
Equality checking. Both `Expr.eqv` and `Expr.equal` are implemented in C++.
-/
/-- info: true -/
#guard_msgs in #eval Expr.eqv (mkLet `n default default default) (mkLet `n default default default)
/-- info: false -/
#guard_msgs in #eval Expr.eqv (mkLet `n default default default) (mkHave `n default default default)
/-- info: false -/
#guard_msgs in #eval Expr.eqv (mkHave `n default default default) (mkLet `n default default default)
/-- info: true -/
#guard_msgs in #eval Expr.eqv (mkHave `n default default default) (mkHave `n default default default)
/-- info: true -/
#guard_msgs in #eval Expr.equal (mkLet `n default default default) (mkLet `n default default default)
/-- info: false -/
#guard_msgs in #eval Expr.equal (mkLet `n default default default) (mkHave `n default default default)
/-- info: false -/
#guard_msgs in #eval Expr.equal (mkHave `n default default default) (mkLet `n default default default)
/-- info: true -/
#guard_msgs in #eval Expr.equal (mkHave `n default default default) (mkHave `n default default default)

/-!
Inequality checking. This too is implemented in C++.
-/
/-- info: false -/
#guard_msgs in #eval Expr.lt (mkLet `n default default default) (mkLet `n default default default)
/-- info: true -/
#guard_msgs in #eval Expr.lt (mkLet `n default default default) (mkHave `n default default default)
/-- info: false -/
#guard_msgs in #eval Expr.lt (mkHave `n default default default) (mkLet `n default default default)
/-- info: false -/
#guard_msgs in #eval Expr.lt (mkHave `n default default default) (mkHave `n default default default)

/-!
Testing toString, which is implemented in C++.
-/
/-- info: "let n : _inhabitedExprDummy := _inhabitedExprDummy; _inhabitedExprDummy" -/
#guard_msgs in #eval toString (mkLet `n default default default)
/-- info: "have n : _inhabitedExprDummy := _inhabitedExprDummy; _inhabitedExprDummy" -/
#guard_msgs in #eval toString (mkHave `n default default default)

/-!
Testing the Lean pretty printer.
-/
elab "eval_expr% " t:term : term => do
  let e ← Elab.Term.elabTermEnsuringType t (mkConst ``Expr)
  unsafe Meta.evalExpr Expr (mkConst ``Expr) e
/--
info: let n := Nat.zero;
n : Nat
-/
#guard_msgs in #check eval_expr% (mkLet `n (mkConst ``Nat) (mkConst ``Nat.zero) (.bvar 0))
/--
info: have n := Nat.zero;
n : Nat
-/
#guard_msgs in #check eval_expr% (mkHave `n (mkConst ``Nat) (mkConst ``Nat.zero) (.bvar 0))

/-!
Testing `Expr.replace`, which is implemented in C++.
The `nondep` flag was previously cleared.
-/
/-- info: Lean.Expr.letE `n (Lean.Expr.bvar 1) (Lean.Expr.bvar 1) (Lean.Expr.bvar 1) true -/
#guard_msgs in #eval Expr.replace (fun e => if let .bvar i := e then some (.bvar (i + 1)) else none) (mkHave `n (.bvar 0) (.bvar 0) (.bvar 0))

/-!
Testing `instantiateMvars`, which is implemented in C++.
The `nondep` flag was previously cleared.
-/
/--
info: Lean.Expr.letE `n (Lean.Expr.const `Nat []) (Lean.Expr.const `Nat.zero []) (Lean.Expr.const `Unit []) true
-/
#guard_msgs in #eval show MetaM Expr from do
  let m ← Meta.mkFreshExprMVar none
  m.mvarId!.assign (mkConst ``Unit)
  Lean.instantiateMVars (Lean.mkLet `n (mkConst ``Nat) (mkConst ``Nat.zero) m true)

namespace TestLambdaLetTelescope
/-!
Check that `lambdaLetTelescope` consumes `haves`. Also checks that `preserveNondepLet := false` turns `have`s into `let`s.
-/
def c : Nat → Nat → Bool := fun x => have y := 1; fun z => x == y + z
/--
info: #[false, true, false]
#[false, false, false]
-/
#guard_msgs in
open Lean Meta in
run_meta do
  let decl ← getConstInfo ``c
  lambdaLetTelescope decl.value! fun xs _ => do
    IO.println <| ← xs.mapM fun x => return (← x.fvarId!.getDecl).isNondep
  lambdaLetTelescope decl.value! (preserveNondepLet := false) fun xs _ => do
    IO.println <| ← xs.mapM fun x => return (← x.fvarId!.getDecl).isNondep
end TestLambdaLetTelescope
