import Lean
new_frontend
open Lean

def x := 10

unsafe def tst : CoreM Unit := do
env ← getEnv;
IO.println $ env.evalConst Nat `x;
pure ()

#eval tst

def f (x : Nat) := x + 1

unsafe def tst2 : CoreM Unit := do
env ← getEnv;
f ← liftIO $ IO.ofExcept $ env.evalConst (Nat → Nat) `f;
IO.println $ (f 10);
pure ()

#eval tst2
