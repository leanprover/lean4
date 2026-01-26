/-
Manual test for the claude tactic with Anthropic API

This file is commented out because it requires an Anthropic API key
which won't be available in CI.

To run this test manually:

1. Get an API key from https://console.anthropic.com/
2. Set the environment variables:
   ```bash
   export ANTHROPIC_API_KEY="your-api-key-here"
   export LEAN_CLAUDE_API=true
   ```
3. Uncomment the test code below
4. Run with:
   ```bash
   cd tests/lean/run
   lake env lean --run claudeAPITest.lean
   ```
   Or from the lean4 root:
   ```bash
   ANTHROPIC_API_KEY="..." LEAN_CLAUDE_API=true \
     build/release/stage1/bin/lean --root=. -Dlinter.all=false \
     tests/lean/run/claudeAPITest.lean
   ```

Expected behavior:
- Claude will suggest tactics like `rfl`, `decide`, `simp` for simple goals
- You should see "Try these:" suggestions with working tactics
- The tactic prints token usage: "API usage: N input tokens, M output tokens"

You can also test with different models:
```lean
set_option tactic.claude.model "claude-sonnet-4-20250514"  -- Default, fast
set_option tactic.claude.model "claude-opus-4-20250514"    -- Most capable
```

And enable prompt tracing:
```lean
set_option trace.claude.prompt true
```
-/

module
public import Lean -- remove after update-stage0

/-
-- Simple test: prove 2 + 2 = 4 (uses default Sonnet 4)
example : 2 + 2 = 4 := by
  claude
  sorry

-- Test with a slightly harder proof
example (x : Nat) : x + 0 = x := by
  claude
  sorry

-- Test with Opus 4 for more capability
set_option tactic.claude.model "claude-opus-4-20250514"

example (n : Nat) : n = n := by
  claude
  sorry

-- Test with prompt tracing
set_option trace.claude.prompt true

example : True := by
  claude
  sorry
-/
