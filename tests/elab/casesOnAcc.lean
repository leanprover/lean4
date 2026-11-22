def result : Nat := Acc.casesOn (Nat.lt_wfRel.wf.apply 37) fun x _ => x

theorem result_eq : result = 37 := by
  rw [result]
  cases result._proof_1
  rfl

/-- info: 37 -/
#guard_msgs in
#eval result
