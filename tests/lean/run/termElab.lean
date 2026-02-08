import Lean


open Lean
open Lean.Elab
open Lean.Elab.Term

def tst1 : TermElabM Unit := do
let opt ← getOptions;
let stx ← `(forall (a b : Nat), Nat);
IO.println "message 1"; -- This message goes direct to stdio. It will be displayed before trace messages.
let e ← elabTermAndSynthesize stx none;
trace[Elab.debug] m!">>> {e}"; -- display message when `trace.Elab.debug` is true
IO.println "message 2"

/--
info: message 1
message 2
-/
#guard_msgs in
#eval tst1

def tst2 : TermElabM Unit := do
let opt ← getOptions;
let a := mkIdent `a;
let b := mkIdent `b;
let stx ← `((fun ($a : Type) (x : $a) => @id $a x) _ 1);
let e ← elabTermAndSynthesize stx none;
trace[Elab.debug] m!">>> {e}";
throwErrorIfErrors

#guard_msgs in
#eval tst2
