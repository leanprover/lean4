example : ¬ true = false := by
  simp [(¬ ·)]

example (h : y = 0) : x + y = x := by
  simp [(.+.)] -- Expands `HAdd.hAdd
  traceState
  simp [Add.add]
  simp [h, Nat.add]
  done

example (h : y = 0) : x + y = x := by
  simp [.+.]
  traceState
  simp [Add.add]
  simp [h, Nat.add]
  done
