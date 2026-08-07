import Lean

open Lean Meta

/-- info: fun {a} => a -/
#guard_msgs in
run_meta
  let e := Expr.lam `a (.sort 0) (.bvar 0) .default
  let (mvars, _, e) ← lambdaMetaTelescope e
  let e ← mkLambdaFVars mvars e
  logInfo m!"{e}"
