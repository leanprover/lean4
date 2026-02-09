theorem ex6 (f : Nat → Nat) (x y z : Nat) (h : (x, z).1 = (fun x => x) y) : f x = f y := by
  simp (config := { beta := false }) at h
  trace_state
  simp at h
  trace_state
  simp [h]
