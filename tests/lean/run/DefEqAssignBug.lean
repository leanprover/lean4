import Lean.Meta



open Lean
open Lean.Meta

def checkM (x : MetaM Bool) : MetaM Unit :=
unless (← x) do throwError "check failed"

def tst1 : MetaM Unit := do
let nat := mkConst `Nat
let m1 ← mkFreshExprMVar nat
let m2 ← mkFreshExprMVar (← mkArrow nat nat)
withLocalDeclD `x nat fun x => do
  let t := mkApp m2 x
  checkM $ isDefEq t m1

def tst2 : MetaM Unit := do
let nat := mkConst `Nat
let m1 ← mkFreshExprMVar nat
let m2 ← mkFreshExprMVar (← mkArrow nat nat)
withLocalDeclD `x nat fun x => do
  let t := mkApp m2 x
  checkM $ isDefEq m1 t

set_option trace.Meta true

#guard_msgs in
#eval tst1

#guard_msgs in
#eval tst2
