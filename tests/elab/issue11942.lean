import Lean

example (a : Nat) (ha : a = 37) :=
  (match a with | 42 => by contradiction | n => n) = 37
