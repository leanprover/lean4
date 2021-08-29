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

theorem ex (x : List Nat) : f x > 0 := by
  simp [f]
  induction x using f.match_1.splitter
  . simp [f.match_1.eq_1]
  . simp [f.match_1.eq_2]
  . rw [f.match_1.eq_3] <;> (first | assumption | decide)
