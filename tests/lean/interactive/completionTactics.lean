/-
This test is fragile because it tests that the full list of tactic completions works correctly.
When adding a new tactic or adjusting the docstring of an existing tactic, this test will break.

If you didn't touch the elaboration infrastructure or the language server,
you can safely assume that this test is still correct and replace the
`completionTactics.lean.expected.out` file with the `completionTactics.lean.produced.out` file
in order to un-break it.
-/

example : True := by  -- No completions expected
                  --^ textDocument/completion

example : True := by  -- All tactic completions expected
                   --^ textDocument/completion

example : True := by ski  -- Tactic completions matching `ski` expected
                      --^ textDocument/completion

example : True := by skip  -- No completions expected
                       --^ textDocument/completion

example : True := by skip;  -- All tactic completions expected
                        --^ textDocument/completion

example : True := by skip;  -- All tactic completions expected
                         --^ textDocument/completion

example : True := by skip; ski  -- Tactic completions matching `ski` expected
                            --^ textDocument/completion

example : True := by
  skip
  skip;  -- All tactic completions expected
     --^ textDocument/completion

example : True := by
    -- All tactic completions expected
--^ textDocument/completion

example : True := by
  sorry
    -- All tactic completions expected
--^ textDocument/completion

example : True := by
    -- All tactic completions expected
--^ textDocument/completion
  sorry

example : True := by
  have : True := by
      -- All tactic completions expected
  --^ textDocument/completion

example : True := by
  have : True := by
      -- All tactic completions expected
--^ textDocument/completion

example : True := by
  have : True := by
    sorry
      -- All tactic completions expected
  --^ textDocument/completion

example : True := by
  have : True := by
    sorry
      -- All tactic completions expected
--^ textDocument/completion

example : True := by
  have : True :=
      -- No completions expected
  --^ textDocument/completion

example : True := by
  have : True :=
      -- All tactic completions expected
--^ textDocument/completion

example : True :=
  have : True := by
      -- All tactic completions expected
  --^ textDocument/completion

example : True :=
  have : True := by
      -- All tactic completions expected
--^ textDocument/completion

example : True :=
  have : True := by
    sorry
      -- All tactic completions expected
  --^ textDocument/completion

example : True :=
  have : True := by
    sorry
      -- No completions expected
--^ textDocument/completion

example (n : Nat) : True := by
  induction n with
  | zero =>   -- All tactic completions expected
          --^ textDocument/completion

example (n : Nat) : True := by
  induction n with
  | zero =>
    sorry
      -- All tactic completions expected
  --^ textDocument/completion

example (n : Nat) : True := by
  induction n with
  | zero =>
    sorry
      -- All tactic completions expected
  --^ textDocument/completion

example (n : Nat) : True := by
  induction n
  ·   -- All tactic completions expected
  --^ textDocument/completion

example : True := by {
    -- All tactic completions expected
--^ textDocument/completion
}
