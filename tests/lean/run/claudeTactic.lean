/-
Tests for the `claude` tactic
-/
module
public import Lean -- remove after update-stage0

-- Test 1: Mock response - tactic that solves goal
set_option tactic.claude.mock "{\"tactics\": [\"rfl\"]}"

/--
info: Try this:
  [apply] rfl
---
error: unsolved goals
⊢ 2 + 2 = 4
-/
#guard_msgs in
example : 2 + 2 = 4 := by
  claude

-- Test 2: Mock response - multiple tactics, some bad
set_option tactic.claude.mock "{\"tactics\": [\"invalid_tactic\", \"trivial\", \"also_invalid\"]}"

/--
info: Try this:
  [apply] trivial
---
error: unsolved goals
⊢ True
-/
#guard_msgs in
example : True := by
  claude

-- Test 3: Mock response - no working tactics
set_option tactic.claude.mock "{\"tactics\": [\"bad_tactic1\", \"bad_tactic2\"]}"

/--
error: Claude suggested no working tactics
-/
#guard_msgs in
example : True := by
  claude

-- Test 4: Mock response - multiple tactics (only one works)
set_option tactic.claude.mock "{\"tactics\": [\"rfl\", \"trivial\"]}"

/--
info: Try this:
  [apply] trivial
---
error: unsolved goals
⊢ True
-/
#guard_msgs in
example : True := by
  claude  -- rfl doesn't work on True, only trivial does

-- Test 5: Test with actual proof
set_option tactic.claude.mock "{\"tactics\": [\"simp\"]}"

/--
info: Try this:
  [apply] simp
---
error: unsolved goals
x : Nat
⊢ x + 0 = x
-/
#guard_msgs in
example (x : Nat) : x + 0 = x := by
  claude

-- Test 6: JSON parse error
set_option tactic.claude.mock "not valid json"

/--
error: Failed to parse Claude response: offset 0: expected: null

Response:
not valid json
-/
#guard_msgs in
example : True := by
  claude

-- Test 7: Wrong JSON format
set_option tactic.claude.mock "{\"wrong_field\": [\"rfl\"]}"

/--
error: Failed to parse Claude response: property not found: tactics

Response:
{"wrong_field": ["rfl"]}
-/
#guard_msgs in
example : True := by
  claude

-- Test 8: Multi-line tactic sequence (newline-separated tactics)
-- This tests that "have h : Nat := 1\nomega" is correctly parsed as two tactics
set_option tactic.claude.mock "{\"tactics\": [\"have h : Nat := 1\\nomega\"]}"

/--
info: Try this:
  [apply] have h : Nat := 1
  omega
---
error: unsolved goals
n : Nat
⊢ n + 1 > n
-/
#guard_msgs in
example (n : Nat) : n + 1 > n := by
  claude
