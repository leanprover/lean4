/-
Test that the claude tactic works with template variable extraction,
including tactic steps before the claude call.
-/
import Lean -- remove after update-stage0

-- Use mock to avoid actually calling Claude
set_option tactic.claude.mock "{\"tactics\": [\"omega\"]}"

-- Enable prompt tracing to verify template variables
set_option trace.claude.prompt true

-- A helper definition to test file context capture
def helper : Nat := 42

-- Test that claude tactic includes prior tactic steps in the declaration
theorem myTheorem (n m : Nat) : n + m = m + n := by
  have h : n = n := rfl
  claude
  omega
