import Lean

/-!
# Tests for `pp.fvars.anonymous`

When a free variable is not in the local context (a "loose" fvar),
the pretty printer renders it with an internal name like `_fvar.42`.
The `pp.fvars.anonymous` option (default `true`) controls this behavior:
when set to `false`, loose fvars are displayed as `_fvar._`.
-/

open Lean Elab Command in
#guard_msgs in
run_cmd liftTermElabM do
  let fvarId : FVarId := { name := .num `_uniq 42 }
  let e := Expr.fvar fvarId
  let fmt ← Meta.ppExpr e
  guard <| s!"{fmt}" == "_fvar.42"

set_option pp.fvars.anonymous false in
open Lean Elab Command in
#guard_msgs in
run_cmd liftTermElabM do
  let fvarId : FVarId := { name := .num `_uniq 42 }
  let e := Expr.fvar fvarId
  let fmt ← Meta.ppExpr e
  guard <| s!"{fmt}" == "_fvar._"
