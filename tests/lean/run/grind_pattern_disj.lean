/-
Tests for grind_pattern with disjunction support (CNF constraints)
-/

-- Positive test cases missing

-- Test 1: Error case - guard in disjunction should be rejected
/--
error: `guard` and `check` constraints cannot be used in disjunctions
-/
#guard_msgs in
grind_pattern mod_eq_of_lt => a % b where
  guard (a < b) or not_value a

-- Test 5: Error case - check in disjunction should be rejected
/--
error: `guard` and `check` constraints cannot be used in disjunctions
-/
#guard_msgs in
grind_pattern mod_eq_of_lt => a % b where
  check (a < b) or not_value a
