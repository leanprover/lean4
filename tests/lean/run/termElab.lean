import Init.Lean

open Lean
open Lean.Elab
open Lean.Elab.Term

set_option trace.Elab.debug true

def tst : TermElabM Unit := do
opt ← getOptions;
stx ← `(fun (a : Nat) => a);
dbgTrace "message 1"; -- This message goes direct to stdio. It will be displayed before trace messages.
e ← elabTermAndSynthesize stx none;
logDbgTrace (">>> " ++ e); -- display message when `trace.Elab.debug` is true
dbgTrace "message 2"

#eval tst
