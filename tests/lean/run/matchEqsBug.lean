import Lean
syntax (name := test) "test%" ident : command

open Lean.Elab
open Lean.Elab.Command

@[command_elab test] def elabTest : CommandElab := fun stx => do
  let id ← resolveGlobalConstNoOverloadWithInfo stx[1]
  liftTermElabM do
    IO.println (repr (← Lean.Meta.Match.getEquationsFor id))
  return ()

def f (x : List Nat) : Nat :=
  match x with
  | [] => 1
  | [a] => 2
  | _ => 3


def g (x : Unit) (y : Bool) : Unit :=
  match x, y with
  | _, true => ()
  | x,    _ => x

set_option trace.Meta.Match.matchEqs true
test% f.match_1
#check f.match_1.splitter

def g.match_1.splitter := 4

test% g.match_1
#check g.match_1.eq_1
#check g.match_1.eq_2
#check g.match_1.splitter
