import Init.Lean
open Lean

def x := 10

unsafe def tst : MetaIO Unit := do
env ← MetaIO.getEnv;
IO.println $ env.evalConst Nat `x;
pure ()

#eval tst
