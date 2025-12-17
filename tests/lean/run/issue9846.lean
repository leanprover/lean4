def testMatch : Array α → Unit
  | #[_] => ()
  | _ => ()

/--
error: Failed to realize constant testMatch.match_1.eq_1:
  Incomplete case splitting during match compilation, goal left-hand side not fully reduced to an application of a match alternative:
    (⋯ ▸ fun h => ⋯ ▸ h_1 (x✝¹.getLit 0 ⋯ ⋯)) ⋯ ≍ h_2 x✝
---
error: Unknown constant `testMatch.match_1.eq_1`
-/
#guard_msgs in
#print testMatch.match_1.eq_1
