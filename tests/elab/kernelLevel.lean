import Lean.CoreM

/-! Regression tests for kernel `Level` operations via `Kernel.check`/`Kernel.whnf`. -/

universe u_1

open Lean

/--
info: Lean.Expr.sort (Lean.Level.succ (Lean.Level.succ (Lean.Level.param `u_1)))
-/
#guard_msgs in
#eval show CoreM Expr from do
  let env ← getEnv
  let u : Level := .param `u_1
  let ty := Expr.forallE `x (.sort (.succ u)) (.sort (.succ .zero)) .default
  let some t := (Kernel.check env {} ty).toOption | return default
  -- `mk_max (succ (succ u_1)) 2`: was `max (succ (succ u_1)) 2`, now `succ (succ u_1)` (subsumes rule)
  return t
