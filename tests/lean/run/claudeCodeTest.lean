/-
Manual test for the claude tactic with real Claude Code CLI

This file is commented out because it requires the Claude Code CLI to be available
and the environment variable to be set, which won't be true in CI.

To run this test manually:

1. Ensure you have Claude Code CLI installed and in your PATH
2. Set the environment variable:
   ```bash
   export LEAN_CLAUDE_CODE=true
   ```
3. Uncomment the test code below
4. Run with:
   ```bash
   cd tests/lean/run
   lake env lean --run claudeCodeTest.lean
   ```
   Or from the lean4 root:
   ```bash
   LEAN_CLAUDE_CODE=true build/release/stage1/bin/lean \
     --root=. -Dlinter.all=false tests/lean/run/claudeCodeTest.lean
   ```

Expected behavior:
- Claude will suggest tactics like `rfl`, `decide`, `simp` for simple goals
- You should see "Try these:" suggestions with working tactics
- The tactic prints "Run /usage in Claude Code to check usage"
-/

module
public import Lean -- remove after update-stage0

/-
-- Simple test: prove 2 + 2 = 4
example : 2 + 2 = 4 := by
  claude
  sorry  -- We'll see what Claude suggests

-- Test with a slightly harder proof
example (x : Nat) : x + 0 = x := by
  claude
  sorry
-/
