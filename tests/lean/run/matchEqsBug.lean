import Lean
syntax (name := test) "test%" ident : command

open Lean.Elab
open Lean.Elab.Command

@[commandElab test] def elabTest : CommandElab := fun stx => do
  let id ← resolveGlobalConstNoOverloadWithInfo stx[1]
  liftTermElabM none do
    Lean.Meta.Match.mkEquationsFor id
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
test% g.match_1
