/-
Test that the claude tactic works with template variable extraction.
-/
import Lean -- remove after update-stage0

-- Use mock to avoid actually calling Claude
set_option tactic.claude.mock "{\"tactics\": [\"rfl\"]}"

-- Enable prompt tracing to verify template variables
set_option trace.claude.prompt true

-- A helper definition to test file context capture
def helper : Nat := 42

-- Test that claude tactic runs and extracts context
theorem myTheorem (n : Nat) : n = n := by
  claude
  rfl
