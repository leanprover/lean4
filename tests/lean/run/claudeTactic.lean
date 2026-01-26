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

-- Test 9: Type error - exact with wrong type should be filtered out
-- "exact 42" doesn't work for goal `True`, should not be suggested
set_option tactic.claude.mock "{\"tactics\": [\"exact 42\", \"trivial\"]}"

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

-- Test 10: Reference to non-existent hypothesis should be filtered out
set_option tactic.claude.mock "{\"tactics\": [\"exact nonexistent_hyp\", \"trivial\"]}"

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

-- Test 11: All tactics have type errors - should get "no working tactics"
set_option tactic.claude.mock "{\"tactics\": [\"exact 42\", \"exact \\\"hello\\\"\", \"exact [1,2,3]\"]}"

/--
error: Claude suggested no working tactics
-/
#guard_msgs in
example : True := by
  claude

-- Test 12: Multi-line where second tactic has type error
-- "have h : Nat := 1\nexact h" - h is Nat but goal is True, should fail
set_option tactic.claude.mock "{\"tactics\": [\"have h : Nat := 1\\nexact h\", \"trivial\"]}"

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

-- Test 13: Tactic that parses but fails at runtime (apply to wrong goal)
set_option tactic.claude.mock "{\"tactics\": [\"apply Nat.add_comm\", \"rfl\"]}"

/--
info: Try this:
  [apply] rfl
---
error: unsolved goals
⊢ 1 = 1
-/
#guard_msgs in
example : 1 = 1 := by
  claude

-- Test 14: Using undefined lemma should be filtered
set_option tactic.claude.mock "{\"tactics\": [\"exact this_lemma_does_not_exist\", \"rfl\"]}"

/--
info: Try this:
  [apply] rfl
---
error: unsolved goals
n : Nat
⊢ n = n
-/
#guard_msgs in
example (n : Nat) : n = n := by
  claude

-- Test 15: JSON in ```json code block with explanation text before
set_option tactic.claude.mock "Here's the answer:\n\n```json\n{\"tactics\": [\"rfl\"]}\n```\n"

/--
info: Try this:
  [apply] rfl
---
error: unsolved goals
⊢ 1 = 1
-/
#guard_msgs in
example : 1 = 1 := by
  claude

-- Test 16: Multiple code blocks, JSON is second (after a lean code block)
set_option tactic.claude.mock "Goal:\n```lean\n⊢ True\n```\n\nTry:\n```json\n{\"tactics\": [\"trivial\"]}\n```\n"

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

-- Test 17: JSON without code block markers (inline in text)
set_option tactic.claude.mock "I think this works: {\"tactics\": [\"rfl\"]} is the answer"

/--
info: Try this:
  [apply] rfl
---
error: unsolved goals
⊢ 1 = 1
-/
#guard_msgs in
example : 1 = 1 := by
  claude

-- Test 18: JSON with braces inside tactic strings (tests extractJsonObject)
-- The tactic contains `}` which should not break JSON extraction
set_option tactic.claude.mock "{\"tactics\": [\"sorry } this has braces { inside\", \"trivial\"]}"

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

-- Test 19: Optional string argument with period
set_option tactic.claude.mock "{\"tactics\": [\"trivial\"]}"

/--
info: Try this:
  [apply] trivial
---
error: unsolved goals
⊢ True
-/
#guard_msgs in
example : True := by
  claude "Use trivial here."

-- Test 20: Optional string argument with exclamation mark
set_option tactic.claude.mock "{\"tactics\": [\"rfl\"]}"

/--
info: Try this:
  [apply] rfl
---
error: unsolved goals
⊢ 1 = 1
-/
#guard_msgs in
example : 1 = 1 := by
  claude "This should be reflexivity!"

-- Test 21: Optional string argument with question mark
set_option tactic.claude.mock "{\"tactics\": [\"simp\"]}"

/--
info: Try this:
  [apply] simp
---
error: unsolved goals
n : Nat
⊢ n + 0 = n
-/
#guard_msgs in
example (n : Nat) : n + 0 = n := by
  claude "Can you simplify this?"

-- Test 22: Missing punctuation - should warn and skip
set_option tactic.claude.mock "{\"tactics\": [\"trivial\"]}"

/--
warning: Instruction should end with punctuation (., !, or ?). Skipping Claude query.
---
error: unsolved goals
⊢ True
-/
#guard_msgs in
example : True := by
  claude "No punctuation here"

-- Test 23: Empty string - should proceed normally (no instruction appended)
set_option tactic.claude.mock "{\"tactics\": [\"trivial\"]}"

/--
info: Try this:
  [apply] trivial
---
error: unsolved goals
⊢ True
-/
#guard_msgs in
example : True := by
  claude ""

-- Test 24: Whitespace-only string - should proceed normally
set_option tactic.claude.mock "{\"tactics\": [\"rfl\"]}"

/--
info: Try this:
  [apply] rfl
---
error: unsolved goals
⊢ 2 = 2
-/
#guard_msgs in
example : 2 = 2 := by
  claude "   "
