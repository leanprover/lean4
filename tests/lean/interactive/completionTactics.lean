prelude
import Init.Notation

/-- A docstring -/
syntax (name := skip) "skip" : tactic

/-- Another docstring -/
syntax (name := exact) "exact " term : tactic

example : True := by  -- No completions expected
                  --^ textDocument/completion

example : True := by   -- All tactic completions expected
                   --^ textDocument/completion

example : True := by ski  -- Tactic completions matching `ski` expected
                      --^ textDocument/completion

example : True := by skip  -- No completions expected
                       --^ textDocument/completion

example : True := by skip;  -- All tactic completions expected
                        --^ textDocument/completion

example : True := by skip;  -- All tactic completions expected
                         --^ textDocument/completion

example : True := by
  skip
  skip;  -- All tactic completions expected
     --^ textDocument/completion

example : True := by
    -- All tactic completions expected
--^ textDocument/completion

example : True := by
  skip
    -- All tactic completions expected
--^ textDocument/completion

example : True := by
    -- All tactic completions expected
--^ textDocument/completion
  skip

example : True := by
  exact by
      -- All tactic completions expected
  --^ textDocument/completion

example : True := by
  exact by
      -- All tactic completions expected
--^ textDocument/completion

example : True := by
  exact by
    skip
      -- All tactic completions expected
  --^ textDocument/completion

example : True := by
  exact by
    skip
      -- All tactic completions expected
--^ textDocument/completion

example : True := by
  exact
      -- No completions expected
  --^ textDocument/completion

example : True := by
  exact
      -- All tactic completions expected
--^ textDocument/completion

example : True :=
  let foo := by
      -- All tactic completions expected
  --^ textDocument/completion

example : True :=
  let foo := by
      -- All tactic completions expected
--^ textDocument/completion

example : True :=
  let foo := by
    skip
      -- All tactic completions expected
  --^ textDocument/completion

example : True :=
  let foo := by
    skip
      -- No completions expected
--^ textDocument/completion

example : True := by {
    -- All tactic completions expected
--^ textDocument/completion
}
