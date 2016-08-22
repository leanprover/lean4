open tactic

example (a : nat) : 0 = nat.succ a → false
:= by intro1 >>= cases
