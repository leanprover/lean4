import Lean
syntax (name := test) "test%" ident : command

open Lean.Elab
open Lean.Elab.Command

@[commandElab test] def elabTest : CommandElab := fun stx => do
  let id ← resolveGlobalConstNoOverloadWithInfo stx[1]
  liftTermElabM none do
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

test% Std.RBNode.balance1.match_1
#check @Std.RBNode.balance1.match_1.splitter
