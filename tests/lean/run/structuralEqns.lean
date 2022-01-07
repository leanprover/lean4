import Lean

open Lean
open Lean.Meta
def tst (declName : Name) : MetaM Unit := do
  IO.println (← getUnfoldEqnFor? declName)

#eval tst ``List.map
#check @List.map._eq_1
#check @List.map._eq_2
#check @List.map._unfold

def foo (xs ys zs : List Nat) : List Nat :=
  match (xs, ys) with
  | (xs', ys')   =>
    match zs with
    | z::zs => foo xs ys zs
    | _ => match ys' with
     | [] => [1]
     | _  => [2]

#eval tst ``foo

#check foo._eq_1
#check foo._eq_2
#check foo._unfold

#eval tst ``foo

def g : List Nat → List Nat → Nat
  | [],         y::ys => y
  | [],         ys    => 0
  | [x1],       ys    => g [] ys
  | x::xs,      y::ys => g xs ys + y
  | x::xs,      []    => g xs []

#eval tst ``g
#check g._eq_1
#check g._eq_2
#check g._eq_3
#check g._eq_4
#check g._eq_5
#check g._unfold

def h (xs : List Nat) (y : Nat) : Nat :=
  match xs with
  | [] => y
  | x::xs =>
    match y with
    | 0 => h xs 10
    | y+1 => h xs y

#eval tst ``h
#check h._eq_1
#check h._eq_2
#check h._eq_3
#check h._unfold

def r (i j : Nat) : Nat :=
  i +
    match j with
    | Nat.zero => 1
    | Nat.succ j =>
      i * match j with
          | Nat.zero => 2
          | Nat.succ j => r i j

#eval tst ``r
#check r._eq_1
#check r._eq_2
#check r._eq_3
#check r._unfold

def bla (f g : α → α → α) (a : α) (i : α) (j : Nat) : α :=
  f i <|
    match j with
    | Nat.zero => i
    | Nat.succ j =>
      g i <| match j with
          | Nat.zero => a
          | Nat.succ j => bla f g a i j

#eval tst ``bla
#check @bla._eq_1
#check @bla._eq_2
#check @bla._eq_3
#check @bla._unfold
