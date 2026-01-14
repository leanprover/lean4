example (a b : Nat) (h : a = b):
  (let _ : id Bool := true; a) = (let _ : Bool := true; b) := by
  simp -zeta -zetaDelta [h]
