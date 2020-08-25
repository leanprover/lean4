import Lean

open Lean
open Lean.Elab
open Lean.Elab.Term

set_option trace.Elab.debug true

def tst1 : TermElabM Unit := do
opt ← getOptions;
stx ← `(forall (a b : Nat), Nat);
IO.println "message 1"; -- This message goes direct to stdio. It will be displayed before trace messages.
e ← elabTermAndSynthesize stx none;
logDbgTrace (">>> " ++ e); -- display message when `trace.Elab.debug` is true
IO.println "message 2"

#eval tst1

def tst2 : TermElabM Unit := do
opt ← getOptions;
let a := mkIdent `a;
let b := mkIdent `b;
stx ← `((fun ($a : Type) (x : $a) => @id $a x) _ 1);
e ← elabTermAndSynthesize stx none;
logDbgTrace (">>> " ++ e);
throwErrorIfErrors

#eval tst2
