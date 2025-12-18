/-! should not parse `done` as part of `induction` -/

example (a : Nat) : True := by
  induction a with
  done
