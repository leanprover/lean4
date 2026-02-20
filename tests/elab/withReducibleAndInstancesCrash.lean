import Lean

@[reducible] def foo (x : Nat) := x + 1
@[reducible] def bla (x y : Nat) := foo (foo x) + foo (foo x)
@[reducible] def boo (x y : Nat) := foo (bla (foo x) (foo y) * bla (foo y) (foo x) * bla (foo y) (foo x))

open Lean
open Lean.Meta
def tst : MetaM Unit := do
  let c ← getConstInfo `boo
  lambdaTelescope c.value! fun xs b => do
    withReducibleAndInstances do
      trace[Meta.debug] "b: {← reduce b}"

set_option trace.Meta.debug true
#eval tst
