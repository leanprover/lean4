import Lean.Meta

new_frontend

open Lean
open Lean.Meta

def mkArrow (d b : Expr) : Expr := mkForall `_ BinderInfo.default d b

def checkM (x : MetaM Bool) : MetaM Unit :=
unlessM x $ throwError "check failed"

def tst1 : MetaM Unit := do
let nat := mkConst `Nat;
let m1 ← mkFreshExprMVar nat;
let m2 ← mkFreshExprMVar (mkArrow nat nat);
withLocalDeclD `x nat $ fun x => do
  let t := mkApp m2 x;
  checkM $ isDefEq t m1

def tst2 : MetaM Unit := do
let nat := mkConst `Nat;
let m1 ← mkFreshExprMVar nat;
let m2 ← mkFreshExprMVar (mkArrow nat nat);
withLocalDeclD `x nat $ fun x => do
  let t := mkApp m2 x;
  checkM $ isDefEq m1 t

set_option trace.Meta true

#eval tst1
#eval tst2
