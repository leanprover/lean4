import Lean.CoreM
import Lean.MonadEnv

open Lean
open Lean.Core

def f : CoreM Nat := do
let env ← getEnv;
let cinfo ← getConstInfo `Nat.add;
trace[Elab] "trace message";
IO.println $ toString cinfo.type;
IO.println "testing...";
pure 10;

/--
info: ([mdata borrowed:1 Nat]) -> ([mdata borrowed:1 Nat]) -> Nat
testing...
10
-/
#guard_msgs in
#eval f

set_option trace.Elab true

/--
info: ([mdata borrowed:1 Nat]) -> ([mdata borrowed:1 Nat]) -> Nat
testing...
[Elab] trace message
10
-/
#guard_msgs in
#eval f
