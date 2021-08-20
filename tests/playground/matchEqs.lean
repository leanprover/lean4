import Lean
syntax (name := test) "test%" ident : command

open Lean.Elab
open Lean.Elab.Command

@[commandElab test] def elabTest : CommandElab := fun stx => do
  let id ← resolveGlobalConstNoOverloadWithInfo stx[1]
  liftTermElabM none do
    Lean.Meta.Match.mkEquationsFor id
  return ()

def f (xs ys : List String) : Nat :=
  match xs, ys with
  | [], []      => 0
  | _,  ["abc"] => 1
  | _, x::xs    => xs.length
  | _,  _       => 2


def h (x y : Nat) : Nat :=
  match x, y with
  | 10000, _ => 0
  | 10001, _ => 5
  | _, 20000 => 4
  | x+1, _   => 3
  | Nat.zero, y+1 => 44
  | _, _     => 1

-- theorem ex1 : h 10000 1 = 0 :=
--  rfl

-- theorem ex2 : h 10002 1 = 3 :=
--  rfl

def g (xs ys : Array Nat) : Nat :=
  match xs, ys with
  | #[], #[]     => 0
  | _, #[0, y+1] => 1
  | _, #[x, y]   => 2
  | _,  _        => 3

set_option trace.Meta.debug true
set_option pp.proofs true
-- set_option trace.Meta.debug truen
test% f.match_1
test% h.match_1
-- test% g.match_1
