opaque f : Nat → Nat
axiom f_eq (x : Nat) : f (f x) = x

theorem ex0 (x : Nat) (h : f (f x) = x) : (have y := 0 + x*x; if f (f x) = x then 1 else y + 1) = 1 := by
  simp (config := { zeta := false }) only [h, Nat.zero_add]
  trace_state
  simp

#print ex0 -- uses have_congr

theorem ex1 (x : Nat) (h : f (f x) = x) : (have y := x*x; if f (f x) = x then 1 else y + 1) = 1 := by
  simp (config := { zeta := false }) only [h]
  trace_state
  simp

#print ex1 -- uses have_body_congr

theorem ex2 (x z : Nat) (h : f (f x) = x) (h' : z = x) : (have y := f (f x); y) = z := by
  simp (config := { zeta := false }) only [h]
  trace_state
  simp [h']

#print ex2 -- uses have_val_congr

theorem ex3 (x z : Nat) : (let α := Nat; (fun x : α => 0 + x)) = id := by
  simp (config := { zeta := false, failIfUnchanged := false })
  trace_state -- should not simplify let body since `fun α : Nat => fun x : α => 0 + x` is not type correct
  simp (config := { unfoldPartialApp := true }) [id]

theorem ex4 (p : Prop) (h : p) : (have n := 10; fun x : { z : Nat // z < n } => x = x) = fun z => p := by
  simp (config := { zeta := false })
  trace_state
  simp [h]

#print ex4 -- uses have_body_congr
