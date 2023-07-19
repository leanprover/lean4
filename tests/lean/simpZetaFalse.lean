opaque f : Nat → Nat
axiom f_eq (x : Nat) : f (f x) = x

theorem ex1 (x : Nat) (h : f (f x) = x) : (let y := x*x; if f (f x) = x then 1 else y + 1) = 1 := by
  simp (config := { zeta := false }) only [h]
  trace_state
  simp

#print ex1 -- uses let_congr

theorem ex2 (x z : Nat) (h : f (f x) = x) (h' : z = x) : (let y := f (f x); y) = z := by
  simp (config := { zeta := false }) only [h]
  trace_state
  simp [h']

#print ex2 -- uses let_val_congr

theorem ex3 (x z : Nat) : (let α := Nat; (fun x : α => 0 + x)) = id := by
  simp (config := { zeta := false, failIfUnchanged := false })
  trace_state -- should not simplify let body since `fun α : Nat => fun x : α => 0 + x` is not type correct
  simp [id]

theorem ex4 (p : Prop) (h : p) : (let n := 10; fun x : { z : Nat // z < n } => x = x) = fun z => p := by
  simp (config := { zeta := false })
  trace_state
  simp [h]

#print ex4 -- uses let_body_congr
