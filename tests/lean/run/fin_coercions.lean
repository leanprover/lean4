example (x : Fin (n + 1)) (h : x < n) : Fin (n + 1) := x.succ.castLT (by simp [h])
