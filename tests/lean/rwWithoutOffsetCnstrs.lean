open Lean.Parser.Tactic in
macro "rw0" s:rwRuleSeq : tactic =>
  `(tactic| rw (config := { offsetCnstrs := false }) $s:rwRuleSeq)

example (m n : Nat) : Nat.ble (n+1) (n+0) = false := by
  rw0 [Nat.add_zero]
  trace_state
  admit
