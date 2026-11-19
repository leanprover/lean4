module

import Lean

/-! Regression test for issue #14348: opaque constants of a unit-like type are definitionally equal. -/

opaque a : Unit
opaque b : Unit

example : a = b := rfl

opaque c.{u} : Unit := let _ := Sort u; ()
opaque d.{u} : Unit := let _ := Sort u; ()

example : c.{0} = d.{1} := rfl
example : c.{0} = c.{1} := rfl

opaque e.{u, v} : Unit := let _ := (Sort u → Sort v); ()

open Lean Meta in
run_meta do
  let u ← mkFreshLevelMVar
  let t := mkConst ``e [u, .zero]
  let s := mkConst ``e [.succ .zero, .succ .zero]
  unless ← isDefEq t s do
    throwError "expected the unit-like fallback to succeed"
  unless (← instantiateLevelMVars u) == u do
    throwError "failed level comparison assigned a universe metavariable"
