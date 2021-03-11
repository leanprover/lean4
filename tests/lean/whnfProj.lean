import Lean

def h (x : Nat) := x
def f (x : Nat) := x + 1
def g (x : Nat) := (x, x+1).fst


open Lean
open Lean.Meta

def tst (declName : Name) : MetaM Unit := do
  let c ← getConstInfo declName
  lambdaTelescope c.value! fun _ b => do
    trace[Meta.debug] "1. {b}"
    trace[Meta.debug] "2. {← withReducible <| whnf b}"
    trace[Meta.debug] "3. {← withReducibleAndInstances <| whnf b}"
    trace[Meta.debug] "4. {← withDefault <| whnf b}"
    pure ()

set_option trace.Meta.debug true
#eval tst `f
#eval tst `g
