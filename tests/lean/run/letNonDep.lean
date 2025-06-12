import Lean
/-!
# Tests of `Expr.letE (nonDep := true) ..`

This file exercises the Lean/C++ interface to make sure that the `nonDep` field
is successfully part of the data model.
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
