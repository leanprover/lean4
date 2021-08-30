def f (x : Nat) : Nat :=
  x + (set_option trace.Meta.synthInstance true in 1)

def g (x : Nat) : Nat := 0 + x.succ

theorem ex : f = g := by
  simp only [f]
  set_option trace.Meta.Tactic.simp true in simp only [Nat.add_succ, g]
  simp only [Nat.zero_add]
