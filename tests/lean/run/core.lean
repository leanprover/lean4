import Lean.CoreM
new_frontend
open Lean
open Lean.Core

def f : CoreM Nat := do {
  env ← getEnv;
  cinfo ← getConstInfo `Nat.add;
  trace! `Elab "trace message";
  liftIO $ IO.println $ toString cinfo.type;
  liftIO $ IO.println "testing...";
  pure 10
}

#eval f

set_option trace.Elab true

#eval f
