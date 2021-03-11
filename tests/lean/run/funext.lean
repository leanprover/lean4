theorem ex1 : (fun y => y + 0) = (fun x => 0 + x) := by
  funext x
  simp

theorem ex2 : (fun y x => y + x + 0) = (fun x y => y + x) := by
  funext x y
  rw [Nat.add_zero, Nat.add_comm]

theorem ex3 : (fun (x : Nat × Nat) => x.1 + x.2) = (fun (x : Nat × Nat) => x.2 + x.1) := by
  funext (a, b)
  show a + b = b + a
  rw [Nat.add_comm]

theorem ex4 : (fun (x : Nat × Nat) (y : Nat × Nat) => x.1 + y.2) = (fun (x : Nat × Nat) (z : Nat × Nat) => z.2 + x.1) := by
  funext (a, b) (c, d)
  show a + d = d + a
  rw [Nat.add_comm]

theorem ex5 : (fun (x : Id Nat) => x.succ + 0) = (fun (x : Id Nat) => 0 + x.succ) := by
  funext (x : Nat)
  have y := x + 1 -- if `(x : Nat)` is not used at `funext`, then `x+1` would fail to be elaborated since we don't have the instance `Add (Id Nat)`
  rw [Nat.add_comm]
