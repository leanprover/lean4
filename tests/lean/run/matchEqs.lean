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
  induction x using f.match_1.splitter
  next => simp [f.match_1.eq_1]
  next x => simp [f.match_1.eq_2]
  next x h1 h2 =>
    rw [f.match_1.eq_3]
    . decide
    . exact h1
    . exact h2
