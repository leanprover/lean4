import Lean.Meta.Sym
open Lean Meta Sym Internal


def tst1 : SymM Unit := do
  let x1 ← mkBVarS 0
  let x2 ← mkBVarS 1
  let t1 ← mkAppS (← mkAppS (← mkConstS `f) x1) x2
  let t2 ← mkForallS `x BinderInfo.default (← mkConstS `Nat) t1
  IO.println (← liftLooseBVarsS t1 0 1)
  IO.println (← liftLooseBVarsS t2 0 1)
  let t3 ← lowerLooseBVarsS (← liftLooseBVarsS t2 0 1) 1 1
  IO.println t3
  assert! t2 == t3
  assert! isSameExpr t2 t3

/--
info: f #1 #2
forall (x : Nat), f x #1
forall (x : Nat), f x #0
-/
#guard_msgs in
#eval SymM.run tst1
