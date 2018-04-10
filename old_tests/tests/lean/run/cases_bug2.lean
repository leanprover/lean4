open tactic

example (a : nat) : 0 = nat.succ a → false
:= by do h ← intro1, cases h
