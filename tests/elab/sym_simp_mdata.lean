import Std.Tactic.BVDecide
import Lean
set_option warn.sorry false

open Lean Meta Sym Sym.Simp

theorem notNot (a : Bool) : (!!a) = a := by simp

theorem negToNot (a : Bool) : (¬(a = true)) = ((!a) = true) := by simp

def runSymSimp (e : Expr) : MetaM Expr := SymM.run do
  let methods ← mkMethods #[``notNot, ``negToNot]
  let e ← preprocessExpr e
  let (r, _) ← SimpM.run (Sym.Simp.simp e) methods
  return Result.getResultExpr e r

/--
info: plain:   (!b) = true
---
info: wrapped: (!b) = true
-/
#guard_msgs in
run_meta do
  withLocalDeclD `b (mkConst ``Bool) fun b => do
    -- `(!!b) = true`
    let inner := mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool)
      (mkApp (mkConst ``Bool.not) (mkApp (mkConst ``Bool.not) b)) (mkConst ``Bool.true)
    let plain   := mkApp (mkConst ``Not) inner
    let wrapped := mkApp (mkConst ``Not) (mkAnnotation `noImplicitLambda inner)
    logInfo m!"plain:   {← runSymSimp plain}"
    logInfo m!"wrapped: {← runSymSimp wrapped}"
