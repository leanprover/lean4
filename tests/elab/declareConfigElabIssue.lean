example : True := by
  simp (config := (fun (c : Lean.Meta.Simp.Config) => { c with arith := true }) {})
