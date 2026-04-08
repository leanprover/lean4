prelude
import Init.Notation

/-
This test is a bit brittle because it checks that tactic completion works correctly for all
tactic completions that we get in `prelude` + `import Init.Notation`.
When changing the docstring of any of these tactics, this test will break.

If you didn't touch the elaboration infrastructure or the language server, then you can safely
assume that this test is still correct and unbreak it by overwriting
`completionTactics.lean.expected.out` with `completionTactics.lean.produced.out` after running
this test.
-/

/-- A docstring -/
syntax (name := skip) "skip" : tactic

/-- Another docstring -/
syntax (name := exact) "exact " term : tactic

example : True := by  -- No completions expected
                  --^ completion

example : True := by   -- All tactic completions expected
                   --^ completion

example : True := by ski  -- Tactic completions matching `ski` expected
                      --^ completion

example : True := by skip  -- No completions expected
                       --^ completion

example : True := by skip;  -- All tactic completions expected
                        --^ completion

example : True := by skip;  -- All tactic completions expected
                         --^ completion

example : True := by
  skip
  skip;  -- All tactic completions expected
     --^ completion

example : True := by
    -- All tactic completions expected
--^ completion

example : True := by
  skip
    -- All tactic completions expected
--^ completion

example : True := by
    -- All tactic completions expected
--^ completion
  skip

example : True := by
  exact by
      -- All tactic completions expected
  --^ completion

example : True := by
  exact by
      -- All tactic completions expected
--^ completion

example : True := by
  exact by
    skip
      -- All tactic completions expected
  --^ completion

example : True := by
  exact by
    skip
      -- All tactic completions expected
--^ completion

example : True := by
  exact
      -- No completions expected
  --^ completion

example : True := by
  exact
      -- All tactic completions expected
--^ completion

example : True :=
  let foo := by
      -- All tactic completions expected
  --^ completion

example : True :=
  let foo := by
      -- All tactic completions expected
--^ completion

example : True :=
  let foo := by
    skip
      -- All tactic completions expected
  --^ completion

example : True :=
  let foo := by
    skip
      -- No completions expected
--^ completion

example : True := by {
    -- All tactic completions expected
--^ completion
}

example : True := by
  { skip -- All tactic completions expected
     }
  --^ completion

/-!
Now check that first token detection and tactic names work correctly in completion.
-/

/-- Local def -/
syntax  "let " letDecl : tactic

/-- Local recursive def -/
@[tactic_name "let rec"]
syntax (name := letrec) "let " &"rec" letRecDecls : tactic

example : True := by
                   --^ completion
