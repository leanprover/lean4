example : ¬ true = false := by
  simp [(¬ ·)]

example (h : y = 0) : x + y = x := by
  simp [(.+.)] -- Expands `HAdd.hAdd
  trace_state
  simp [Add.add]
  simp [h, Nat.add]
  done

example (h : y = 0) : x + y = x := by
  simp [.+.]
  trace_state
  simp [Add.add]
  simp [h, Nat.add]
  done
