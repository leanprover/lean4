import Init.Lean
open Lean

def x := 10

unsafe def tst : MetaIO Unit := do
env ← MetaIO.getEnv;
IO.println $ env.evalConst Nat `x;
pure ()

#eval tst

def f (x : Nat) := x + 1

unsafe def tst2 : MetaIO Unit := do
env ← MetaIO.getEnv;
f ← liftM $ IO.ofExcept $ env.evalConst (Nat → Nat) `f;
IO.println $ (f 10);
pure ()

#eval tst2
