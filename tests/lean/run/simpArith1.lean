theorem ex1 : a + b < b + 1 + a + c := by
  simp (config := { arith := true })

theorem ex2 : a + b < b + 1 + a + c := by
  simp +arith

theorem ex3 : a + (fun x => x) b < b + 1 + a + c := by
  simp +arith

theorem ex5 (h : a + d + b > b + 1 + (a + (c + c) + d)) : False := by
  simp +arith at h

#print ex5

theorem ex6 (p : Nat → Prop) (h : p (a + 1 + a + 2 + b)) : p (2*a + b + 3) := by
  simp +arith at h
  assumption

#print ex6
