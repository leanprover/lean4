def f (x : Nat) : Nat :=
  x + (set_option trace.Meta.synthInstance true in 1)

def g (x : Nat) : Nat := 0 + x.succ

theorem ex : f = g := by
  simp (config := { unfoldPartialApp := true }) only [f]
  set_option trace.Meta.Tactic.simp true in simp (config := { unfoldPartialApp := true }) only [Nat.add_succ, g]
  simp (config := { unfoldPartialApp := true }) only [Nat.zero_add]
