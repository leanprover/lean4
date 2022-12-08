import Lean

set_option compiler.checkTypes true

def f1 (x : Option Nat) (y : Nat) : Nat :=
  let z := some y
  if let (some x, some y) := (x, z) then
    x + y
  else
    0

inductive Ty where
 | c1 | c2 | c3 | c4 | c5

def f2 (a b : Ty) (n : Nat) : Nat :=
  let x := match a with
    | .c1 => 10 * n
    | _  => 20 * n
  let y := match b with
    | .c2 => 10 + n
    | _  => 20 + n
  x + y
