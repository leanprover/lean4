import Lean

open Lean
open Lean.Meta
def tst (declName : Name) : MetaM Unit := do
  IO.println (← getUnfoldEqnFor? declName)

def foo (xs ys zs : List Nat) : List Nat :=
  match (xs, ys) with
  | (xs', ys')   =>
    match zs with
    | z::zs => foo xs ys zs
    | _ => match ys' with
     | [] => [1]
     | _  => [2]

/-- info: (some foo.eq_def) -/
#guard_msgs in
#eval tst ``foo

/--
info: foo.eq_def (xs ys zs : List Nat) :
  foo xs ys zs =
    match (xs, ys) with
    | (xs', ys') =>
      match zs with
      | z :: zs => foo xs ys zs
      | x =>
        match ys' with
        | [] => [1]
        | x => [2]
-/
#guard_msgs in
#check foo.eq_def


def bar (xs ys : List Nat) : List Nat :=
  match xs ++ [], ys ++ [] with
  | xs', ys'   => xs' ++ ys'

/--
info: def bar : List Nat → List Nat → List Nat :=
fun xs ys =>
  match xs ++ [], ys ++ [] with
  | xs', ys' => xs' ++ ys'
-/
#guard_msgs in
#print bar  -- should not contain either `let _discr` aux binding
