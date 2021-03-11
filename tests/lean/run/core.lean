import Lean.CoreM

open Lean
open Lean.Core

def f : CoreM Nat := do
let env ← getEnv;
let cinfo ← getConstInfo `Nat.add;
trace[Elab] "trace message";
IO.println $ toString cinfo.type;
IO.println "testing...";
pure 10;

#eval f

set_option trace.Elab true

#eval f
