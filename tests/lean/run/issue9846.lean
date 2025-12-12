def testMatch : Array α → Unit
  | #[_] => ()
  | _ => ()

/--
error: Failed to realize constant testMatch.match_1.eq_1:
  failed to generate equality theorem _private.lean.run.issue9846.0.testMatch.match_1.eq_2 for `match` expression `testMatch.match_1`
  ⏎
  Hint: It may help to include indices of inductive types as discriminants in the `match` expression.
---
error: Unknown constant `testMatch.match_1.eq_1`
-/
#guard_msgs in
#print testMatch.match_1.eq_1
