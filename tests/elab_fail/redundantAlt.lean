def f (x : Nat) : Nat :=
 match x with
 | 0 => 1
 | Nat.succ (Nat.succ x) => 3
 | 2 => 4
 | Nat.succ x => 5
 | 3 => 6
