import Init.Lean.Meta
open Lean
open Lean.Meta

def mkArrow (d b : Expr) : Expr := mkForall `_ BinderInfo.default d b

def check (x : MetaM Bool) : MetaM Unit :=
unlessM x $ throw $ Exception.other "check failed"

def tst1 : MetaM Unit := do
let nat := mkConst `Nat;
m1 ← mkFreshExprMVar nat;
m2 ← mkFreshExprMVar (mkArrow nat nat);
withLocalDecl `x nat BinderInfo.default $ fun x => do
  let t := mkApp m2 x;
  check $ isDefEq t m1

def tst2 : MetaM Unit := do
let nat := mkConst `Nat;
m1 ← mkFreshExprMVar nat;
m2 ← mkFreshExprMVar (mkArrow nat nat);
withLocalDecl `x nat BinderInfo.default $ fun x => do
  let t := mkApp m2 x;
  check $ isDefEq m1 t

set_option trace.Meta true

#eval tst1
#eval tst2
