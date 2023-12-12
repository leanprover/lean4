/-! Test `·` being able to refer to constants in `simp` -/

example : ¬ true = false := by
  simp [(¬ ·)]

/-! Test `binop%` -/

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

/-! Test `binop%` variant `rightact%` as well -/

example (x y : Nat) : x ^ y = y ^ x := by
  simp only [.^.]
