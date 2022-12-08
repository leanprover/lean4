import Lean

open Lean Meta Elab Term in
elab "whnf%" t:term : term <= expectedType => do
  let r ← whnf (← elabTerm t expectedType)
  trace[Meta.debug] "r: {r}"
  return r

opaque x : Option Nat := some 42

set_option trace.Meta.debug true
#eval whnf% x.getD 0
