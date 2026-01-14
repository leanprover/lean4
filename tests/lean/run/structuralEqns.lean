import Lean

open Lean
open Lean.Meta
def tst (declName : Name) : MetaM Unit := do
  IO.println (← getUnfoldEqnFor? declName)

/-- info: (some List.map.eq_def) -/
#guard_msgs in
#eval tst ``List.map
#check @List.map.eq_1
#check @List.map.eq_2
#check @List.map.eq_def

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

#check foo.eq_1
#check foo.eq_2
#check foo.eq_def

/-- info: (some foo.eq_def) -/
#guard_msgs in
#eval tst ``foo

def g : List Nat → List Nat → Nat
  | [],         y::ys => y
  | [],         ys    => 0
  | [x1],       ys    => g [] ys
  | x::xs,      y::ys => g xs ys + y
  | x::xs,      []    => g xs []

/-- info: (some g.eq_def) -/
#guard_msgs in
#eval tst ``g
#check g.eq_1
#check g.eq_2
#check g.eq_3
#check g.eq_4
#check g.eq_5
#check g.eq_def

def h (xs : List Nat) (y : Nat) : Nat :=
  match xs with
  | [] => y
  | x::xs =>
    match y with
    | 0 => h xs 10
    | y+1 => h xs y

/-- info: (some h.eq_def) -/
#guard_msgs in
#eval tst ``h
#check h.eq_1
#check h.eq_2
#check h.eq_def

def r (i j : Nat) : Nat :=
  i +
    match j with
    | Nat.zero => 1
    | Nat.succ j =>
      i * match j with
          | Nat.zero => 2
          | Nat.succ j => r i j

/-- info: (some r.eq_def) -/
#guard_msgs in
#eval tst ``r
#check r.eq_1
#check r.eq_2
#check r.eq_3
#check r.eq_def

def bla (f g : α → α → α) (a : α) (i : α) (j : Nat) : α :=
  f i <|
    match j with
    | Nat.zero => i
    | Nat.succ j =>
      g i <| match j with
          | Nat.zero => a
          | Nat.succ j => bla f g a i j

/-- info: (some bla.eq_def) -/
#guard_msgs in
#eval tst ``bla
#check @bla.eq_1
#check @bla.eq_2
#check @bla.eq_3
#check @bla.eq_def
