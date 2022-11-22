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

test% f.match_1
#check @f.match_1
#check @f.match_1.splitter

theorem ex (x : List Nat) : f x > 0 := by
  simp [f]
  split <;> decide

test% Lean.RBNode.balance1.match_1
#check @Lean.RBNode.balance1.match_1.splitter
