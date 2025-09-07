module
-- In the following test, the first 8 case-splits are irrelevant,
-- and non-chronological backtracking is used to avoid searching
-- (2^8 - 1) irrelevant branches
/--
trace: [grind.split] p8 ∨ q8, generation: 0
[grind.split] p7 ∨ q7, generation: 0
[grind.split] p6 ∨ q6, generation: 0
[grind.split] p5 ∨ q5, generation: 0
[grind.split] p4 ∨ q4, generation: 0
[grind.split] p3 ∨ q3, generation: 0
[grind.split] p2 ∨ q2, generation: 0
[grind.split] p1 ∨ q1, generation: 0
[grind.split] ¬p ∨ ¬q, generation: 0
-/
#guard_msgs (trace) in
set_option trace.grind.split true in
theorem ex
    : p ∨ q →
      ¬ p ∨ q →
      p ∨ ¬ q →
      ¬ p ∨ ¬ q →
      p1 ∨ q1 →
      p2 ∨ q2 →
      p3 ∨ q3 →
      p4 ∨ q4 →
      p5 ∨ q5 →
      p6 ∨ q6 →
      p7 ∨ q7 →
      p8 ∨ q8 →
      False := by
  grind (splits := 10)
