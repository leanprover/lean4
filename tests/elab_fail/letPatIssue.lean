example (x : Nat × Nat) : x.1 + x.2 ≥ 0 :=
  let (a, b) := x
  _

example (x : Nat × Nat) : x.1 + x.2 ≥ 0 :=
  have (a, b) := x
  _

example (x : Nat × Nat) : x.1 + x.2 ≥ 0 := by
  let (a, b) := x
  done

example (x : Nat × Nat) : x.1 + x.2 ≥ 0 := by
  have (a, b) := x
  done

def f : Nat × Nat → Nat
  | (a, b) => a + b + 1

example (x : Nat × Nat) : f x > 0 := by
  let (a, b) := x
  done
