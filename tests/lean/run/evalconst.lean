import Lean
open Lean

def x := 10

unsafe def tst : CoreM Unit := do
env ← Core.getEnv;
IO.println $ env.evalConst Nat `x;
pure ()

#eval tst

def f (x : Nat) := x + 1

unsafe def tst2 : CoreM Unit := do
env ← Core.getEnv;
f ← liftIO $ IO.ofExcept $ env.evalConst (Nat → Nat) `f;
IO.println $ (f 10);
pure ()

#eval tst2
