import Lean

open Lean

def x := 10

unsafe def tst : CoreM Unit := do
let env ← getEnv
IO.println $ env.evalConst Nat {} `x

#eval tst

def f (x : Nat) := x + 1

unsafe def tst2 : CoreM Unit := do
let env ← getEnv
let f ←  IO.ofExcept $ env.evalConst (Nat → Nat) {} `f
IO.println $ (f 10)

#eval tst2
