import Lean

open Lean
open Lean.Meta
def tst (declName : Name) : MetaM Unit := do
  IO.println (← getEqnsFor? declName)

#eval tst ``List.map
#check @List.map.eq_1
#check @List.map.eq_2

def foo (xs ys zs : List Nat) : List Nat :=
  match (xs, ys) with
  | (xs', ys')   =>
    match zs with
    | z::zs => foo xs ys zs
    | _ => match ys' with
     | [] => [1]
     | _  => [2]

#eval tst ``foo

#check foo.eq_1
#check foo.eq_2

#eval tst ``foo

def g : List Nat → List Nat → Nat
  | [],         y::ys => y
  | [],         ys    => 0
  | [x1],       ys    => g [] ys
  | x::xs,      y::ys => g xs ys + y
  | x::xs,      []    => g xs []

#eval tst ``g
#check g.eq_1
#check g.eq_2
#check g.eq_3
#check g.eq_4
#check g.eq_5

def h (xs : List Nat) (y : Nat) : Nat :=
  match xs with
  | [] => y
  | x::xs =>
    match y with
    | 0 => h xs 10
    | y+1 => h xs y

#eval tst ``h
#check h.eq_1
#check h.eq_2
#check h.eq_3
