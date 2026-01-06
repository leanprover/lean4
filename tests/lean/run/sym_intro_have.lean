import Lean.Meta.Tactic
import Lean.Meta.Sym

def f (x : Nat) :=
  let y := x + 1
  2*y

open Lean Meta Sym
/--
info: x : Nat
⊢ have y := x + 1;
  x ≤ 2 * y
---
info: x : Nat
y : Nat := x + 1
⊢ x ≤ 2 * y
-/
#guard_msgs in
run_meta SymM.run do
  withLocalDeclD `x Nat.mkType fun x => do
  let m ← mkFreshExprMVar <| mkNatLE x (mkApp (mkConst ``f) x)
  let mvarId := m.mvarId!
  let mvarId ← unfoldTarget mvarId ``f
  let mvarId ← mvarId.liftLets
  logInfo mvarId
  let (_, mvarId) ← intro mvarId `y
  logInfo mvarId
  return ()
