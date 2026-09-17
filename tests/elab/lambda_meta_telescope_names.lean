import Lean

open Lean Meta

/-! `lambdaMetaTelescope` should preserve binder names (#14264). -/

/-- info: fun a => a -/
#guard_msgs in
run_meta
  let e := Expr.lam `a (.sort 0) (.bvar 0) .default
  let (mvars, _, e) ← lambdaMetaTelescope e
  let e ← mkLambdaFVars mvars e
  logInfo m!"{e}"

/-- info: fun {x} => x -/
#guard_msgs in
run_meta
  let e := Expr.lam `x (.sort 0) (.bvar 0) .implicit
  let (mvars, _, e) ← lambdaMetaTelescope e
  let e ← mkLambdaFVars mvars e
  logInfo m!"{e}"
