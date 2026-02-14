import Lean.Meta.Sym.Simp.ArithNorm
import Lean.Meta.Sym.Simp.Main

/-!
# Tests for the arithmetic normalizer simproc in Sym.simp

Tests that the `mkArithNormSimproc` correctly normalizes ring expressions
to polynomial normal form.
-/

set_option maxRecDepth 4000

open Lean Meta Sym Sym.Simp in
private def runArithNorm (mkExpr : MetaM Expr) : MetaM String := do
  SymM.run do
    let arithNorm ← mkArithNormSimproc
    let e ← shareCommon (← mkExpr)
    let r ← SimpM.run' (arithNorm e) {} {}
    match r with
    | .step e' _ _ => return s!"{← ppExpr e'}"
    | .rfl _ => return s!"rfl({← ppExpr e})"

-- Basic arithmetic on Int
/-- info: "5" -/
#guard_msgs in
open Lean Meta in
#eval runArithNorm (mkAppM ``HAdd.hAdd #[mkIntLit 2, mkIntLit 3])

/-- info: "6" -/
#guard_msgs in
open Lean Meta in
#eval runArithNorm (mkAppM ``HMul.hMul #[mkIntLit 2, mkIntLit 3])

/-- info: "-1" -/
#guard_msgs in
open Lean Meta in
#eval runArithNorm (mkAppM ``HSub.hSub #[mkIntLit 2, mkIntLit 3])

-- Symbolic: (a + b) + (a + b) normalizes to 2*a + 2*b
/-- info: "2 * ?a + 2 * ?b" -/
#guard_msgs in
open Lean Meta in
#eval show MetaM String from do
  let a ← mkFreshExprMVar (mkConst ``Int)
  a.mvarId!.setUserName `a
  let b ← mkFreshExprMVar (mkConst ``Int)
  b.mvarId!.setUserName `b
  let ab ← mkAppM ``HAdd.hAdd #[a, b]
  runArithNorm (mkAppM ``HAdd.hAdd #[ab, ab])
