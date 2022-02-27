theorem ex1 : a + b < b + 1 + a + c := by
  simp (config := { arith := true })

theorem ex2 : a + b < b + 1 + a + c := by
  simp_arith

theorem ex3 : a + (fun x => x) b < b + 1 + a + c := by
  simp_arith

theorem ex4 : a + (fun x => x) b < b + 1 + a + c := by
  simp_arith (config := { beta := false })
  trace_state
  simp_arith

theorem ex5 (h : a + d + b > b + 1 + (a + (c + c) + d)) : False := by
  simp_arith at h

#print ex5
