import Lean
open Lean

/--
info: let y : Type := Prop;
let x : y := True;
p x
---
info: let y : Type := Prop;
let x : y := True;
x
---
info: let y : Type := Prop;
y
-/
#guard_msgs in
set_option pp.letVarTypes true in
example (p : ∀ a, a) :
    (let y := Prop; let x : y := True; p x) = p True := by
  run_tac
    let env ← Lean.getEnv
    let lctx ← getLCtx
    let_expr Eq _ lhs _ := (← Elab.Tactic.getMainTarget) | unreachable!
    logInfo lhs
    let ty ← ofExceptKernelException <| Lean.Kernel.check env lctx lhs
    logInfo ty
    let sort ← ofExceptKernelException <| Lean.Kernel.check env lctx ty
    logInfo sort
  trivial
