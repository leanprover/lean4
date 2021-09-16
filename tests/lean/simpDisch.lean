constant f : Nat → Nat
@[simp] axiom fEq (x : Nat) (h : x ≠ 0) : f x = x

example (x : Nat) (h : x ≠ 0) : f x = x + 0 := by
  simp (discharger := traceState; exact (fun h' => h') h)

example (x y : Nat) (h1 : x ≠ 0) (h2 : y ≠ 0) (h3 : x = y) : f x = f y + 0 := by
  simp (discharger := traceState; assumption)
  assumption

example (x y : Nat) (h1 : x ≠ 0) (h2 : y ≠ 0) (h3 : x = y) : f x = f y + 0 := by
  simp (discharger := assumption)
  assumption

example (x y : Nat) (h1 : x ≠ 0) (h2 : y ≠ 0) (h3 : x = y) : f x = f y + 0 := by
  simp (disch := assumption)
  assumption

example (x y : Nat) (h1 : x ≠ 0) (h2 : y ≠ 0) (h3 : x = y) : f x = f y + 0 := by
  conv => lhs; simp (disch := assumption)
  traceState
  conv => rhs; simp (disch := assumption)
  traceState
  assumption
