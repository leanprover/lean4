#check
  let_fun f x := x * 2
  let_fun x := 1
  let_fun y := x + 1
  f (y + x)

example (a b : Nat) (h1 : a = 0) (h2 : b = 0) : (let_fun x := a + 1; x + x) > b := by
  simp (config := { beta := false }) [h1]
  trace_state
  simp (config := { decide := true }) [h2]
