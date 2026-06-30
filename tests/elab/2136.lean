opaque bar : Nat → Nat
theorem foo : bar (Nat.succ a) = 0 := sorry
example : bar (a + 1) = 0 := by with_reducible exact foo -- ok
example : bar (a + a + 1) = 0 := by with_reducible exact foo -- should also work

def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

example (a : Nat) : factorial (a + 1) = (a + 1) * factorial a := by
  rw [factorial] -- works

example (a b : Nat) : factorial ((a + b) + 1) = ((a + b) + 1) * factorial (a + b) := by
  rw [factorial] -- should also work
